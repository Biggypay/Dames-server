-- ============================================================
--  MOTEUR DE MATCHMAKING ATOMIQUE + PRÉSENCE FIABLE — 2026-07-12
--  (migrations déjà appliquées sur le projet Supabase MindSpille :
--   « matchmaking_engine_atomic_join » ; archive de référence)
-- ============================================================
--
--  OBJECTIF
--  Supporter des centaines/milliers de joueurs en recherche simultanée
--  sans aucun conflit d'appariement, et une présence en ligne exacte
--  en temps réel.
--
--  ARCHITECTURE
--  • Tout l'appariement passe par UNE fonction serveur SECURITY DEFINER
--    (matchmaking_join), sérialisée PAR TYPE DE JEU via un verrou
--    advisory transactionnel : le claim client (source de conflits à
--    3+ joueurs) disparaît.
--  • FIFO équitable : l'adversaire le plus ancien de la file est servi
--    en premier ; à 3 joueurs, deux sont appariés, le 3e attend.
--  • Idempotente : rappelée après un match, elle renvoie le même match.
--  • Chaque appel rafraîchit le TTL de l'entrée de file (10 min) : la
--    recherche survit à une sortie de l'application ; sans battement de
--    cœur (polling 3 s côté client), l'entrée expire d'elle-même.
--  • Présence : job pg_cron (chaque minute) qui éteint is_online après
--    45 s sans heartbeat → plus de joueurs « fantômes » en ligne quand
--    l'app PWA est tuée brutalement.
--
--  TEST VALIDÉ (2026-07-12, transaction annulée après lecture) :
--    A join → waiting ; B join → matched(A) instantané ;
--    C join → waiting (pas de conflit) ; A re-join → même game_id.
-- ============================================================

CREATE OR REPLACE FUNCTION public.matchmaking_join(
  p_game_type  text,
  p_bet_amount numeric DEFAULT 50,
  p_settings   jsonb   DEFAULT '{}'::jsonb
) RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public
AS $$
DECLARE
  v_me       uuid := auth.uid();
  v_gt       public.game_type;
  v_opp      uuid;
  v_game_id  uuid;
  v_existing record;
  v_settings jsonb   := coalesce(p_settings, '{}'::jsonb);
  v_bet      numeric := coalesce(p_bet_amount, 50);
BEGIN
  IF v_me IS NULL THEN
    RAISE EXCEPTION 'not_authenticated' USING ERRCODE = '28000';
  END IF;

  BEGIN
    v_gt := p_game_type::public.game_type;
  EXCEPTION WHEN invalid_text_representation THEN
    RAISE EXCEPTION 'invalid_game_type';
  END;

  IF v_bet < 0 OR v_bet > 1000000 THEN v_bet := 50; END IF;
  IF jsonb_typeof(v_settings) IS DISTINCT FROM 'object'
     OR pg_column_size(v_settings) > 8192 THEN
    v_settings := '{}'::jsonb;
  END IF;

  -- Sérialisation par type de jeu : la section critique dure ~1 ms.
  PERFORM pg_advisory_xact_lock(hashtext('matchmaking:' || v_gt::text));

  -- 0) Idempotence : une partie de matchmaking fraîche m'attend déjà ?
  SELECT g.id, g.player1_id, g.player2_id INTO v_existing
  FROM public.games g
  WHERE g.status = 'waiting'
    AND g.game_type = v_gt
    AND g.player1_id IS NOT NULL AND g.player2_id IS NOT NULL
    AND (g.player1_id = v_me OR g.player2_id = v_me)
    AND g.pregame_started_at > now() - interval '2 minutes'
  ORDER BY g.created_at DESC
  LIMIT 1;
  IF FOUND THEN
    DELETE FROM public.matchmaking_queue WHERE user_id = v_me;
    RETURN jsonb_build_object(
      'status', 'matched',
      'game_id', v_existing.id,
      'opponent_id', CASE WHEN v_existing.player1_id = v_me
                          THEN v_existing.player2_id ELSE v_existing.player1_id END,
      'created_by_me', v_existing.player1_id = v_me
    );
  END IF;

  -- 1) Purge des entrées expirées de ce jeu (la table reste minuscule)
  DELETE FROM public.matchmaking_queue
  WHERE game_type = v_gt AND expires_at < now();

  -- 2) Claim atomique : l'adversaire en attente le plus ancien (FIFO)
  SELECT q.user_id INTO v_opp
  FROM public.matchmaking_queue q
  WHERE q.game_type = v_gt
    AND q.user_id <> v_me
    AND q.expires_at > now()
  ORDER BY q.created_at
  FOR UPDATE SKIP LOCKED
  LIMIT 1;

  IF v_opp IS NOT NULL THEN
    DELETE FROM public.matchmaking_queue WHERE user_id IN (v_me, v_opp);
    INSERT INTO public.games (
      game_type, player1_id, player2_id,
      bet_amount, player1_bet_amount, player2_bet_amount,
      player1_is_ready, player2_is_ready,
      is_sandbox, status, pregame_started_at, game_settings
    ) VALUES (
      v_gt, v_me, v_opp, 50, 50, 50, false, false, true, 'waiting', now(), v_settings
    ) RETURNING id INTO v_game_id;
    RETURN jsonb_build_object(
      'status', 'matched', 'game_id', v_game_id,
      'opponent_id', v_opp, 'created_by_me', true
    );
  END IF;

  -- 3) Personne de disponible → je m'inscris / rafraîchis mon entrée
  INSERT INTO public.matchmaking_queue (user_id, game_type, bet_amount, is_sandbox, expires_at)
  VALUES (v_me, v_gt, v_bet, true, now() + interval '10 minutes')
  ON CONFLICT (user_id) DO UPDATE
    SET game_type  = EXCLUDED.game_type,
        bet_amount = EXCLUDED.bet_amount,
        expires_at = EXCLUDED.expires_at;
  RETURN jsonb_build_object('status', 'waiting');
END $$;

REVOKE ALL ON FUNCTION public.matchmaking_join(text, numeric, jsonb) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.matchmaking_join(text, numeric, jsonb) TO authenticated;

-- Présence : filet de sécurité serveur contre les « fantômes » en ligne
CREATE INDEX IF NOT EXISTS idx_profiles_online_seen
  ON public.profiles (last_seen_at) WHERE is_online;

SELECT cron.schedule(
  'prune_stale_online_status',
  '* * * * *',
  $cron$UPDATE public.profiles SET is_online = false
        WHERE is_online AND last_seen_at < now() - interval '45 seconds'$cron$
);

-- ============================================================
--  À APPLIQUER PLUS TARD — re-durcissement RLS de la file
--  ⚠️ SEULEMENT après publication du frontend branché sur
--  matchmaking_join (l'ancien frontend fait encore le claim côté
--  client et a besoin des politiques ouvertes du 2026-07-11).
--  Une fois le nouveau frontend en production, la file n'a plus
--  besoin d'être ouverte : chacun ne gère que SA propre ligne.
-- ============================================================
-- DROP POLICY IF EXISTS "Authenticated users can delete queue entries for matchmaking" ON public.matchmaking_queue;
-- CREATE POLICY "Users can delete own queue entries"
--   ON public.matchmaking_queue FOR DELETE TO authenticated
--   USING (auth.uid() = user_id);
-- DROP POLICY IF EXISTS "Authenticated users can update queue entries" ON public.matchmaking_queue;
-- CREATE POLICY "Users can update own queue entries"
--   ON public.matchmaking_queue FOR UPDATE TO authenticated
--   USING (auth.uid() = user_id) WITH CHECK (auth.uid() = user_id);
-- DROP POLICY IF EXISTS "Authenticated users can insert queue entries" ON public.matchmaking_queue;
-- CREATE POLICY "Users can insert own queue entry"
--   ON public.matchmaking_queue FOR INSERT TO authenticated
--   WITH CHECK (auth.uid() = user_id);
