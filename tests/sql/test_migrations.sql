\set ON_ERROR_STOP on

-- ══════════════════════════════════════════════════════════════════════
--  Jeu d'essai : un tournoi en cours, un duel de groupe deja tranche
--  dont le vainqueur a ete propage au tour suivant.
-- ══════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION pg_temp.seed() RETURNS void LANGUAGE plpgsql AS $$
DECLARE
  t uuid := '11111111-1111-4111-8111-111111111111';
  p1 uuid := '22222222-2222-4222-8222-222222222222';
  p2 uuid := '33333333-3333-4333-8333-333333333333';
  adm uuid := '44444444-4444-4444-8444-444444444444';
  m_a uuid := '55555555-5555-4555-8555-555555555555';
  m_b uuid := '66666666-6666-4666-8666-666666666666';
BEGIN
  DELETE FROM public.notifications;
  DELETE FROM public.admin_logs;
  DELETE FROM public.games;
  DELETE FROM public.tournament_matches;
  DELETE FROM public.tournament_participants;
  DELETE FROM public.tournaments;
  DELETE FROM public.user_roles;
  DELETE FROM auth.users;

  INSERT INTO auth.users (id, email) VALUES (adm, 'admin@mindspille.test'), (p1, 'p1@test'), (p2, 'p2@test');
  INSERT INTO public.user_roles (user_id, role) VALUES (adm, 'admin');

  INSERT INTO public.tournaments (id, name, game_type, status)
  VALUES (t, 'Tournoi de test', 'checkers', 'in_progress');

  INSERT INTO public.tournament_participants (tournament_id, user_id, status, eliminated_at_round)
  VALUES (t, p1, 'active', NULL), (t, p2, 'eliminated', 'group');

  -- Tour suivant : le vainqueur y occupe deja une case.
  INSERT INTO public.tournament_matches (id, tournament_id, round, bracket_position, player1_id, status, scheduled_at)
  VALUES (m_b, t, 'round_of_16', 1, p1, 'pending', now() + interval '1 day');

  -- Le duel litigieux.
  INSERT INTO public.tournament_matches (
    id, tournament_id, round, group_letter, bracket_position, next_match_id,
    player1_id, player2_id, winner_id, loser_id, score, status,
    scheduled_at, played_at, player1_joined_at, player2_joined_at,
    forfeit_processed, start_notified_at, reminder_notified_5min
  ) VALUES (
    m_a, t, 'group', 'A', 3, m_b,
    p1, p2, p1, p2, 'win', 'completed',
    now() - interval '2 hours', now() - interval '90 minutes',
    now() - interval '100 minutes', now() - interval '95 minutes',
    true, now() - interval '2 hours', true
  );
END;
$$;

SELECT pg_temp.seed();

-- ══════════════════════════════════════════════════════════════════════
--  1. Un non-administrateur ne peut pas faire rejouer un match
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE v_err text;
BEGIN
  PERFORM set_config('test.uid', '22222222-2222-4222-8222-222222222222', false);
  PERFORM set_config('test.role', 'authenticated', false);
  BEGIN
    PERFORM public.tournament_replay_match('55555555-5555-4555-8555-555555555555');
    RAISE EXCEPTION 'ECHEC : un joueur a pu rejouer un match';
  EXCEPTION WHEN insufficient_privilege THEN
    RAISE NOTICE 'OK  un joueur ordinaire est refuse (forbidden)';
  END;
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  2. Refus quand le tour suivant est deja lance
-- ══════════════════════════════════════════════════════════════════════
DO $$
BEGIN
  PERFORM set_config('test.uid', '44444444-4444-4444-8444-444444444444', false);
  UPDATE public.tournament_matches SET status = 'in_progress'
   WHERE id = '66666666-6666-4666-8666-666666666666';
  BEGIN
    PERFORM public.tournament_replay_match('55555555-5555-4555-8555-555555555555');
    RAISE EXCEPTION 'ECHEC : le tour suivant etait lance et le rejeu a ete accepte';
  EXCEPTION WHEN check_violation THEN
    IF SQLERRM <> 'next_round_already_started' THEN
      RAISE EXCEPTION 'ECHEC : mauvaise erreur -> %', SQLERRM;
    END IF;
    RAISE NOTICE 'OK  refus quand le tour suivant est lance';
  END;
  UPDATE public.tournament_matches SET status = 'pending'
   WHERE id = '66666666-6666-4666-8666-666666666666';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  3. Rejeu nominal
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  m_a uuid := '55555555-5555-4555-8555-555555555555';
  m_b uuid := '66666666-6666-4666-8666-666666666666';
  p1 uuid := '22222222-2222-4222-8222-222222222222';
  p2 uuid := '33333333-3333-4333-8333-333333333333';
  v_result jsonb;
  v_match public.tournament_matches%rowtype;
  v_next public.tournament_matches%rowtype;
  v_count integer;
BEGIN
  PERFORM set_config('test.uid', '44444444-4444-4444-8444-444444444444', false);
  v_result := public.tournament_replay_match(m_a);

  IF (v_result ->> 'success') <> 'true' THEN
    RAISE EXCEPTION 'ECHEC : reponse inattendue %', v_result;
  END IF;

  SELECT * INTO v_match FROM public.tournament_matches WHERE id = m_a;
  IF v_match.status <> 'ready' THEN RAISE EXCEPTION 'ECHEC : statut = %', v_match.status; END IF;
  IF v_match.winner_id IS NOT NULL OR v_match.loser_id IS NOT NULL OR v_match.score IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : le resultat precedent n''a pas ete efface';
  END IF;
  IF v_match.player1_joined_at IS NOT NULL OR v_match.player2_joined_at IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : les presences precedentes subsistent';
  END IF;
  IF v_match.forfeit_processed OR v_match.result_conflict OR v_match.reminder_notified_5min THEN
    RAISE EXCEPTION 'ECHEC : drapeaux non reinitialises';
  END IF;
  IF v_match.start_notified_at IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : le match ne sera pas re-annonce par le planificateur';
  END IF;
  IF v_match.scheduled_at < now() - interval '1 minute' THEN
    RAISE EXCEPTION 'ECHEC : creneau non rouvert (%)', v_match.scheduled_at;
  END IF;
  IF v_match.player1_id <> p1 OR v_match.player2_id <> p2 THEN
    RAISE EXCEPTION 'ECHEC : les joueurs du duel ont change';
  END IF;
  RAISE NOTICE 'OK  le duel est remis a jouer, creneau rouvert';

  SELECT * INTO v_next FROM public.tournament_matches WHERE id = m_b;
  IF v_next.player1_id IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : le vainqueur precedent occupe encore le tour suivant';
  END IF;
  RAISE NOTICE 'OK  le tour suivant a ete libere';

  SELECT count(*) INTO v_count FROM public.tournament_participants
   WHERE user_id IN (p1, p2) AND status = 'active' AND eliminated_at_round IS NULL;
  IF v_count <> 2 THEN RAISE EXCEPTION 'ECHEC : participants remis en lice = %', v_count; END IF;
  RAISE NOTICE 'OK  les deux joueurs sont de nouveau actifs';

  SELECT count(*) INTO v_count FROM public.notifications
   WHERE data->>'kind' = 'tournament_match_replay';
  IF v_count <> 2 THEN RAISE EXCEPTION 'ECHEC : notifications = %', v_count; END IF;
  RAISE NOTICE 'OK  les deux joueurs sont prevenus';

  SELECT count(*) INTO v_count FROM public.admin_logs WHERE action = 'tournament_match_replay';
  IF v_count <> 1 THEN RAISE EXCEPTION 'ECHEC : trace administrative = %', v_count; END IF;
  RAISE NOTICE 'OK  trace administrative ecrite';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  4. Une partie encore ouverte sur ce duel est close proprement
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  m_a uuid := '55555555-5555-4555-8555-555555555555';
  g uuid;
  v_status public.game_status;
  v_result public.game_result;
BEGIN
  PERFORM pg_temp.seed();
  PERFORM set_config('test.uid', '44444444-4444-4444-8444-444444444444', false);

  INSERT INTO public.games (game_type, player1_id, player2_id, bet_amount, status,
                            started_at, tournament_match_id, is_tournament)
  VALUES ('checkers', '22222222-2222-4222-8222-222222222222',
          '33333333-3333-4333-8333-333333333333', 0, 'in_progress',
          now() - interval '10 minutes', m_a, true)
  RETURNING id INTO g;
  UPDATE public.tournament_matches SET game_id = g WHERE id = m_a;

  PERFORM public.tournament_replay_match(m_a);

  SELECT status, result INTO v_status, v_result FROM public.games WHERE id = g;
  IF v_status <> 'completed' OR v_result <> 'mutual_quit' THEN
    RAISE EXCEPTION 'ECHEC : la partie ouverte n''a pas ete close (% / %)', v_status, v_result;
  END IF;
  IF (SELECT game_id FROM public.tournament_matches WHERE id = m_a) IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : le duel pointe encore sur l''ancienne partie';
  END IF;
  RAISE NOTICE 'OK  la partie encore ouverte est close sans vainqueur';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  5. get_game_resume_offer : les trois situations qui comptent
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  p1 uuid := '22222222-2222-4222-8222-222222222222';
  p2 uuid := '33333333-3333-4333-8333-333333333333';
  g uuid;
  v_rows integer;
  v_both boolean;
  v_waiting boolean;
  v_seconds integer;
BEGIN
  PERFORM pg_temp.seed();
  PERFORM set_config('test.uid', p1::text, false);

  -- (a) partie qui vient de naitre : aucune offre, aucun verdict.
  INSERT INTO public.games (game_type, player1_id, player2_id, bet_amount, status, started_at, is_tournament)
  VALUES ('checkers', p1, p2, 0, 'in_progress', now() - interval '30 seconds', true)
  RETURNING id INTO g;
  SELECT count(*) INTO v_rows FROM public.get_game_resume_offer(g);
  IF v_rows <> 0 THEN
    RAISE EXCEPTION 'ECHEC : une partie de 30 secondes declenche deja la fenetre';
  END IF;
  RAISE NOTICE 'OK  aucune fenetre pendant la formation de la salle';

  -- (b) salle vivante : jamais « les deux joueurs sont deconnectes ».
  UPDATE public.games SET started_at = now() - interval '10 minutes',
                          server_live_at = now() - interval '5 seconds'
   WHERE id = g;
  SELECT both_players_disconnected, opponent_waiting
    INTO v_both, v_waiting
    FROM public.get_game_resume_offer(g);
  IF v_both THEN
    RAISE EXCEPTION 'ECHEC : salle vivante et pourtant « les deux deconnectes »';
  END IF;
  IF NOT v_waiting THEN
    RAISE EXCEPTION 'ECHEC : l''adversaire devrait etre annonce present';
  END IF;
  RAISE NOTICE 'OK  salle vivante : aucun verdict de double deconnexion';

  -- (c) salle morte et personne depuis longtemps : le vrai cas subsiste.
  UPDATE public.games SET server_live_at = now() - interval '10 minutes',
                          player1_last_heartbeat = now() - interval '5 minutes',
                          player2_last_heartbeat = now() - interval '5 minutes'
   WHERE id = g;
  SELECT both_players_disconnected, seconds_remaining
    INTO v_both, v_seconds
    FROM public.get_game_resume_offer(g);
  IF NOT v_both THEN
    RAISE EXCEPTION 'ECHEC : une vraie double deconnexion n''est plus detectee';
  END IF;
  IF v_seconds <> 0 THEN
    RAISE EXCEPTION 'ECHEC : delai restant inattendu (%)', v_seconds;
  END IF;
  RAISE NOTICE 'OK  la vraie double deconnexion est toujours detectee';

  -- (d) mon propre plateau est ouvert : le compte a rebours reste honnete.
  UPDATE public.games SET player1_last_heartbeat = now(),
                          player2_last_heartbeat = now() - interval '5 minutes'
   WHERE id = g;
  SELECT both_players_disconnected, seconds_remaining
    INTO v_both, v_seconds
    FROM public.get_game_resume_offer(g);
  IF v_both OR v_seconds <= 0 THEN
    RAISE EXCEPTION 'ECHEC : joueur present et pourtant delai ecoule (%, %)', v_both, v_seconds;
  END IF;
  RAISE NOTICE 'OK  un joueur present garde du temps devant lui';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  6. save_game_server_room_states ecrit la presence reelle
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  p1 uuid := '22222222-2222-4222-8222-222222222222';
  p2 uuid := '33333333-3333-4333-8333-333333333333';
  g uuid;
  h1 timestamptz;
  h2 timestamptz;
BEGIN
  PERFORM pg_temp.seed();
  INSERT INTO public.games (game_type, player1_id, player2_id, bet_amount, status, started_at, is_tournament)
  VALUES ('checkers', p1, p2, 0, 'in_progress', now() - interval '10 minutes', true)
  RETURNING id INTO g;

  -- Seul le joueur 1 a son socket ouvert.
  PERFORM public.save_game_server_room_states(jsonb_build_array(jsonb_build_object(
    'game_type', 'dames', 'room_id', g::text, 'game_id', g::text, 'status', 'waiting',
    'connected_players', jsonb_build_array(p1::text),
    'state', jsonb_build_object('players', jsonb_build_object())
  )));

  SELECT player1_last_heartbeat, player2_last_heartbeat INTO h1, h2 FROM public.games WHERE id = g;
  IF h1 IS NULL THEN RAISE EXCEPTION 'ECHEC : presence du joueur 1 non enregistree'; END IF;
  IF h2 IS NOT NULL THEN RAISE EXCEPTION 'ECHEC : un joueur absent a ete declare present'; END IF;
  RAISE NOTICE 'OK  seule la presence reelle est enregistree';

  -- Un ancien serveur de jeu (sans le champ) ne casse rien.
  PERFORM public.save_game_server_room_states(jsonb_build_array(jsonb_build_object(
    'game_type', 'dames', 'room_id', g::text, 'game_id', g::text, 'status', 'playing',
    'state', jsonb_build_object('players', jsonb_build_object())
  )));
  IF (SELECT server_live_at FROM public.games WHERE id = g) IS NULL THEN
    RAISE EXCEPTION 'ECHEC : la pulsation de salle a ete perdue';
  END IF;
  RAISE NOTICE 'OK  compatible avec un serveur de jeu non encore deploye';
END;
$$;

\echo 'TOUS LES TESTS SONT PASSES'
