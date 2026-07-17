-- A completed tournament game must advance the bracket atomically.  The game
-- result itself is written only by the trusted game server; this trigger
-- validates the game/match binding again before using that result.
CREATE OR REPLACE FUNCTION public.advance_tournament_from_completed_game()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_match public.tournament_matches%ROWTYPE;
  v_score text;
BEGIN
  IF TG_OP <> 'UPDATE'
     OR NEW.status <> 'completed'::public.game_status
     OR OLD.status = 'completed'::public.game_status THEN
    RETURN NEW;
  END IF;

  -- Ordinary games are never allowed to affect a tournament.
  IF COALESCE(NEW.is_tournament, false) IS NOT TRUE
     AND NEW.tournament_match_id IS NULL THEN
    RETURN NEW;
  END IF;

  -- A tournament game is bound in both directions.  Accept either side of an
  -- existing binding, then repair the missing opposite side in this same
  -- transaction.  A contradictory binding is rejected and the game result is
  -- rolled back instead of advancing the wrong bracket match.
  SELECT tm.*
    INTO v_match
    FROM public.tournament_matches tm
   WHERE tm.id = NEW.tournament_match_id
      OR tm.game_id = NEW.id
   FOR UPDATE;

  IF NOT FOUND THEN
    RAISE EXCEPTION 'tournament_game_without_match';
  END IF;

  IF NEW.tournament_match_id IS NOT NULL
     AND v_match.id <> NEW.tournament_match_id THEN
    RAISE EXCEPTION 'tournament_game_binding_mismatch';
  END IF;

  IF v_match.game_id IS NOT NULL AND v_match.game_id <> NEW.id THEN
    RAISE EXCEPTION 'tournament_match_already_bound_to_another_game';
  END IF;

  IF NOT (
    (NEW.player1_id = v_match.player1_id AND NEW.player2_id = v_match.player2_id)
    OR
    (NEW.player1_id = v_match.player2_id AND NEW.player2_id = v_match.player1_id)
  ) THEN
    RAISE EXCEPTION 'tournament_game_players_do_not_match_bracket';
  END IF;

  UPDATE public.tournament_matches
     SET game_id = NEW.id,
         status = CASE WHEN status = 'ready'::public.tournament_match_status
                       THEN 'in_progress'::public.tournament_match_status
                       ELSE status END,
         updated_at = now()
   WHERE id = v_match.id;

  IF NEW.tournament_match_id IS NULL OR COALESCE(NEW.is_tournament, false) IS NOT TRUE THEN
    UPDATE public.games
       SET tournament_match_id = v_match.id,
           is_tournament = true,
           updated_at = now()
     WHERE id = NEW.id;
  END IF;

  -- A tournament cannot advance on a draw, a mutual quit or an abandoned
  -- match.  Leave the bracket ready for a rematch and flag it for the admin.
  IF NEW.winner_id IS NULL
     OR NEW.result NOT IN ('win'::public.game_result,
                           'loss'::public.game_result,
                           'timeout'::public.game_result) THEN
    UPDATE public.tournament_matches
       SET game_id = NULL,
           status = 'ready'::public.tournament_match_status,
           result_conflict = true,
           updated_at = now()
     WHERE id = v_match.id
       AND status NOT IN ('completed'::public.tournament_match_status,
                          'walkover'::public.tournament_match_status,
                          'cancelled'::public.tournament_match_status);
    RETURN NEW;
  END IF;

  IF NEW.winner_id <> v_match.player1_id AND NEW.winner_id <> v_match.player2_id THEN
    RAISE EXCEPTION 'tournament_winner_not_in_bracket_match';
  END IF;

  IF v_match.status IN ('completed'::public.tournament_match_status,
                        'walkover'::public.tournament_match_status,
                        'cancelled'::public.tournament_match_status) THEN
    IF v_match.winner_id IS DISTINCT FROM NEW.winner_id THEN
      RAISE EXCEPTION 'tournament_match_already_resolved_with_a_different_winner';
    END IF;
    RETURN NEW;
  END IF;

  v_score := NULLIF(trim(COALESCE(NEW.game_settings ->> 'score', '')), '');
  PERFORM public.advance_tournament_match_core(v_match.id, NEW.winner_id,
                                                COALESCE(v_score, NEW.result::text));
  RETURN NEW;
END;
$$;

REVOKE ALL ON FUNCTION public.advance_tournament_from_completed_game() FROM PUBLIC;
REVOKE ALL ON FUNCTION public.advance_tournament_from_completed_game() FROM anon;
REVOKE ALL ON FUNCTION public.advance_tournament_from_completed_game() FROM authenticated;

DROP TRIGGER IF EXISTS trg_advance_tournament_from_game_completion ON public.games;
CREATE TRIGGER trg_advance_tournament_from_game_completion
AFTER UPDATE OF status ON public.games
FOR EACH ROW
WHEN (NEW.status = 'completed'::public.game_status
      AND OLD.status IS DISTINCT FROM 'completed'::public.game_status)
EXECUTE FUNCTION public.advance_tournament_from_completed_game();
