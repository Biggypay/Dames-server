-- REJOUER UN MATCH DE TOURNOI (administrateur)
--
-- Un tournoi avance tout seul, et c'est ce qu'on veut. Mais quand un match a
-- été tranché par un incident plutôt que par le jeu — un forfait injuste, une
-- panne réseau, un plateau qui n'a jamais démarré — il n'existait aucun moyen
-- de rendre la partie aux deux joueurs : le bracket était figé et le perdant
-- éliminé pour de bon.
--
-- Cette fonction remet UN duel dans l'état « à jouer », rouvre son créneau
-- immédiatement (ou à l'heure choisie), et prévient les deux joueurs. Elle ne
-- touche à rien d'autre : les autres matchs, les autres tours et les résultats
-- déjà acquis restent exactement où ils sont.
--
-- Elle refuse de le faire quand cela falsifierait un match déjà joué : si le
-- tour suivant est lancé ou terminé, le vainqueur y a déjà affronté quelqu'un,
-- et le rejouer réécrirait l'histoire d'un troisième joueur.

CREATE OR REPLACE FUNCTION public.tournament_replay_match(
  p_match_id uuid,
  p_scheduled_at timestamptz DEFAULT NULL
)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_match public.tournament_matches%rowtype;
  v_tournament public.tournaments%rowtype;
  v_next public.tournament_matches%rowtype;
  v_third public.tournament_matches%rowtype;
  v_previous_winner uuid;
  v_previous_loser uuid;
  v_when timestamptz;
  v_live_game uuid;
  v_admin_email text;
BEGIN
  IF NOT public.is_tournament_operator() THEN
    RAISE EXCEPTION 'forbidden' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO v_match
    FROM public.tournament_matches
   WHERE id = p_match_id
   FOR UPDATE;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'match_not_found' USING ERRCODE = 'P0002';
  END IF;

  -- Rejouer suppose deux joueurs réels. Une place vacante ne se rejoue pas :
  -- elle se pourvoit (repêchage).
  IF v_match.player1_id IS NULL OR v_match.player2_id IS NULL THEN
    RAISE EXCEPTION 'match_needs_two_players' USING ERRCODE = '23514';
  END IF;
  IF v_match.player1_id = v_match.player2_id THEN
    RAISE EXCEPTION 'match_needs_two_players' USING ERRCODE = '23514';
  END IF;

  SELECT * INTO v_tournament
    FROM public.tournaments
   WHERE id = v_match.tournament_id
   FOR UPDATE;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'tournament_not_found' USING ERRCODE = 'P0002';
  END IF;

  -- Un tournoi terminé a désigné un champion et, selon le réglage, versé des
  -- prix. On ne rouvre pas cela d'un clic.
  IF v_tournament.status NOT IN ('awaiting_start', 'in_progress') THEN
    RAISE EXCEPTION 'tournament_not_replayable' USING ERRCODE = '23514';
  END IF;

  v_when := COALESCE(p_scheduled_at, now());
  v_previous_winner := v_match.winner_id;
  v_previous_loser := v_match.loser_id;

  -- Le tour suivant ne doit pas avoir commencé.
  IF v_match.next_match_id IS NOT NULL THEN
    SELECT * INTO v_next
      FROM public.tournament_matches
     WHERE id = v_match.next_match_id
     FOR UPDATE;
    IF FOUND
       AND (v_next.status IN ('completed', 'walkover', 'in_progress')
            OR v_next.game_id IS NOT NULL) THEN
      RAISE EXCEPTION 'next_round_already_started' USING ERRCODE = '23514';
    END IF;
  END IF;

  -- Même règle pour la petite finale, qui reçoit les perdants des demies.
  IF v_match.round = 'semi' THEN
    SELECT * INTO v_third
      FROM public.tournament_matches
     WHERE tournament_id = v_match.tournament_id
       AND round = 'third_place'
     FOR UPDATE;
    IF FOUND
       AND (v_third.status IN ('completed', 'walkover', 'in_progress')
            OR v_third.game_id IS NOT NULL) THEN
      RAISE EXCEPTION 'third_place_already_started' USING ERRCODE = '23514';
    END IF;
  END IF;

  -- Une partie encore ouverte sur ce duel est close proprement avant tout le
  -- reste : sans cela, son résultat retomberait sur le match rejoué.
  SELECT id INTO v_live_game
    FROM public.games
   WHERE tournament_match_id = v_match.id
     AND status = 'in_progress'::public.game_status
   ORDER BY created_at DESC
   LIMIT 1;

  IF v_live_game IS NOT NULL THEN
    PERFORM set_config('app.trusted_game_write', '1', true);
    UPDATE public.games
       SET status = 'completed'::public.game_status,
           result = 'mutual_quit'::public.game_result,
           winner_id = NULL,
           completed_at = now(),
           updated_at = now()
     WHERE id = v_live_game
       AND status = 'in_progress'::public.game_status;
    PERFORM set_config('app.trusted_game_write', '', true);
  END IF;

  -- Le vainqueur précédent quitte la case qu'il occupait au tour suivant.
  IF v_previous_winner IS NOT NULL AND v_next.id IS NOT NULL THEN
    UPDATE public.tournament_matches
       SET player1_id = CASE WHEN player1_id = v_previous_winner THEN NULL ELSE player1_id END,
           player2_id = CASE WHEN player2_id = v_previous_winner THEN NULL ELSE player2_id END,
           player1_joined_at = CASE WHEN player1_id = v_previous_winner THEN NULL ELSE player1_joined_at END,
           player2_joined_at = CASE WHEN player2_id = v_previous_winner THEN NULL ELSE player2_joined_at END,
           player1_last_seen_at = CASE WHEN player1_id = v_previous_winner THEN NULL ELSE player1_last_seen_at END,
           player2_last_seen_at = CASE WHEN player2_id = v_previous_winner THEN NULL ELSE player2_last_seen_at END,
           status = CASE WHEN status = 'ready' THEN 'pending'::public.tournament_match_status ELSE status END,
           start_notified_at = NULL,
           final_reminder_notified_at = NULL,
           reminder_notified_5min = false,
           updated_at = now()
     WHERE id = v_next.id
       AND (player1_id = v_previous_winner OR player2_id = v_previous_winner);
  END IF;

  -- Idem pour le perdant d'une demi-finale, placé d'office en petite finale.
  IF v_match.round = 'semi' AND v_previous_loser IS NOT NULL AND v_third.id IS NOT NULL THEN
    UPDATE public.tournament_matches
       SET player1_id = CASE WHEN player1_id = v_previous_loser THEN NULL ELSE player1_id END,
           player2_id = CASE WHEN player2_id = v_previous_loser THEN NULL ELSE player2_id END,
           status = CASE WHEN status = 'ready' THEN 'pending'::public.tournament_match_status ELSE status END,
           updated_at = now()
     WHERE id = v_third.id
       AND (player1_id = v_previous_loser OR player2_id = v_previous_loser);
  END IF;

  -- Le duel repart de zéro, créneau rouvert.
  UPDATE public.tournament_matches
     SET winner_id = NULL,
         loser_id = NULL,
         score = NULL,
         game_id = NULL,
         status = 'ready'::public.tournament_match_status,
         scheduled_at = v_when,
         ready_at = NULL,
         played_at = NULL,
         player1_joined_at = NULL,
         player2_joined_at = NULL,
         player1_last_seen_at = NULL,
         player2_last_seen_at = NULL,
         player1_reported_winner = NULL,
         player2_reported_winner = NULL,
         forfeit_processed = false,
         result_conflict = false,
         vacancy_propagated_at = NULL,
         lockout_notified_1h = false,
         reminder_notified_5min = false,
         start_notified_at = NULL,
         final_reminder_notified_at = NULL,
         updated_at = now()
   WHERE id = v_match.id;

  -- Les deux joueurs reviennent en lice. Un match à rejouer n'a pas de perdant.
  UPDATE public.tournament_participants
     SET status = 'active',
         eliminated_at_round = NULL,
         final_rank = NULL,
         updated_at = now()
   WHERE tournament_id = v_match.tournament_id
     AND user_id IN (v_match.player1_id, v_match.player2_id);

  INSERT INTO public.notifications (user_id, type, title, message, data, status)
  SELECT player_id,
         'admin_announcement',
         '🔁 Votre match est à rejouer',
         'L''organisation a décidé de faire rejouer votre match de '
           || COALESCE(v_tournament.game_type, 'tournoi') || '. Rendez-vous à '
           || to_char(v_when AT TIME ZONE 'America/Port-au-Prince', 'HH24:MI')
           || ' (heure d''Haïti) — vous avez une heure pour rejoindre.',
         jsonb_build_object(
           'kind', 'tournament_match_replay',
           'tournament_id', v_match.tournament_id,
           'match_id', v_match.id,
           'game_type', v_tournament.game_type,
           'scheduled_at', v_when,
           'join_deadline', v_when + interval '1 hour',
           'url', '/tournament-match/' || v_match.id::text
         ),
         'unread'
    FROM unnest(ARRAY[v_match.player1_id, v_match.player2_id]) AS player_id
   WHERE player_id IS NOT NULL;

  -- Trace administrative. Elle ne doit jamais faire échouer la remise en jeu.
  BEGIN
    SELECT email INTO v_admin_email FROM auth.users WHERE id = auth.uid();
    IF auth.uid() IS NOT NULL THEN
      INSERT INTO public.admin_logs (admin_id, admin_email, action, target_user_id, details, status)
      VALUES (
        auth.uid(),
        COALESCE(v_admin_email, 'inconnu'),
        'tournament_match_replay',
        v_previous_loser,
        jsonb_build_object(
          'tournament_id', v_match.tournament_id,
          'match_id', v_match.id,
          'round', v_match.round::text,
          'previous_status', v_match.status::text,
          'previous_winner_id', v_previous_winner,
          'previous_loser_id', v_previous_loser,
          'closed_game_id', v_live_game,
          'scheduled_at', v_when
        ),
        'success'
      );
    END IF;
  EXCEPTION WHEN OTHERS THEN
    NULL;
  END;

  RETURN jsonb_build_object(
    'success', true,
    'match_id', v_match.id,
    'status', 'ready',
    'scheduled_at', v_when,
    'join_deadline', v_when + interval '1 hour',
    'player1_id', v_match.player1_id,
    'player2_id', v_match.player2_id,
    'previous_winner_id', v_previous_winner,
    'next_match_cleared', v_next.id,
    'server_now', now()
  );
EXCEPTION WHEN OTHERS THEN
  PERFORM set_config('app.trusted_game_write', '', true);
  RAISE;
END;
$function$;

REVOKE ALL ON FUNCTION public.tournament_replay_match(uuid, timestamptz) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.tournament_replay_match(uuid, timestamptz) TO authenticated;

COMMENT ON FUNCTION public.tournament_replay_match(uuid, timestamptz) IS
  'Administrateur : remet un duel de tournoi à jouer, rouvre son créneau et prévient les deux joueurs. Refuse si le tour suivant est déjà lancé.';
