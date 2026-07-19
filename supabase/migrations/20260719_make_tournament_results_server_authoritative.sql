-- Player reports are useful for dispute evidence, but they are not proof of a
-- result.  Only the trusted completed-game trigger or an authorized
-- administrator may advance a tournament bracket and settle prizes.
CREATE OR REPLACE FUNCTION public.tournament_report_result(
  p_match_id uuid,
  p_winner_id uuid
)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_user_id uuid := auth.uid();
  v_match public.tournament_matches%rowtype;
  v_player1_report uuid;
  v_player2_report uuid;
  v_admin uuid;
BEGIN
  IF v_user_id IS NULL THEN
    RAISE EXCEPTION 'unauthenticated';
  END IF;

  SELECT * INTO v_match
    FROM public.tournament_matches
   WHERE id = p_match_id
   FOR UPDATE;

  IF NOT FOUND THEN
    RAISE EXCEPTION 'match_not_found';
  END IF;
  IF v_match.status IN ('completed', 'walkover', 'cancelled') THEN
    RETURN jsonb_build_object(
      'status', 'completed',
      'winner_id', v_match.winner_id,
      'authoritative', true
    );
  END IF;
  IF v_user_id NOT IN (v_match.player1_id, v_match.player2_id) THEN
    RAISE EXCEPTION 'not_a_participant';
  END IF;
  IF p_winner_id IS NULL OR p_winner_id NOT IN (v_match.player1_id, v_match.player2_id) THEN
    RAISE EXCEPTION 'winner_not_in_match';
  END IF;

  IF v_user_id = v_match.player1_id THEN
    UPDATE public.tournament_matches
       SET player1_reported_winner = p_winner_id, updated_at = now()
     WHERE id = p_match_id;
  ELSE
    UPDATE public.tournament_matches
       SET player2_reported_winner = p_winner_id, updated_at = now()
     WHERE id = p_match_id;
  END IF;

  SELECT player1_reported_winner, player2_reported_winner
    INTO v_player1_report, v_player2_report
    FROM public.tournament_matches
   WHERE id = p_match_id;

  IF v_player1_report IS NOT NULL AND v_player2_report IS NOT NULL THEN
    IF v_player1_report = v_player2_report THEN
      UPDATE public.tournament_matches
         SET result_conflict = false, updated_at = now()
       WHERE id = p_match_id;

      RETURN jsonb_build_object(
        'status', 'reported_waiting_server',
        'reported_winner_id', v_player1_report,
        'authoritative', false
      );
    END IF;

    UPDATE public.tournament_matches
       SET result_conflict = true, updated_at = now()
     WHERE id = p_match_id;

    FOR v_admin IN
      SELECT user_id
        FROM public.user_roles
       WHERE role IN ('admin', 'super_admin')
    LOOP
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      VALUES (
        v_admin,
        'admin_warning',
        '⚠️ Résultat de tournoi contesté',
        'Les deux joueurs ont déclaré des vainqueurs différents. Le serveur n’a attribué aucune victoire ; un arbitrage peut être nécessaire.',
        jsonb_build_object(
          'tournament_id', v_match.tournament_id,
          'match_id', p_match_id,
          'kind', 'tournament_result_conflict'
        ),
        'unread'
      );
    END LOOP;

    RETURN jsonb_build_object('status', 'conflict', 'authoritative', false);
  END IF;

  RETURN jsonb_build_object('status', 'reported_waiting_server', 'authoritative', false);
END;
$$;

REVOKE ALL ON FUNCTION public.tournament_report_result(uuid, uuid) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.tournament_report_result(uuid, uuid) TO authenticated;

COMMENT ON FUNCTION public.tournament_report_result(uuid, uuid) IS
  'Records participant claims only. Never advances a bracket or settles tournament prizes.';
