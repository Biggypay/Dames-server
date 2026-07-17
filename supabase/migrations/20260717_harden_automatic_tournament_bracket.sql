-- Harden the initial automatic-bracket trigger: explicitly reject conflicting
-- bidirectional links and treat a missing game result as needing a rematch.
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

  IF COALESCE(NEW.is_tournament, false) IS NOT TRUE
     AND NEW.tournament_match_id IS NULL THEN
    RETURN NEW;
  END IF;

  SELECT tm.*
    INTO v_match
    FROM public.tournament_matches tm
   WHERE tm.id = NEW.tournament_match_id
   FOR UPDATE;

  IF NOT FOUND THEN
    SELECT tm.*
      INTO v_match
      FROM public.tournament_matches tm
     WHERE tm.game_id = NEW.id
     FOR UPDATE;
    IF NOT FOUND THEN
      RAISE EXCEPTION 'tournament_game_without_match';
    END IF;
  ELSIF EXISTS (
    SELECT 1
      FROM public.tournament_matches tm
     WHERE tm.game_id = NEW.id
       AND tm.id <> v_match.id
  ) THEN
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

  IF NEW.winner_id IS NULL
     OR COALESCE(NEW.result::text, '') NOT IN ('win', 'loss', 'timeout') THEN
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
