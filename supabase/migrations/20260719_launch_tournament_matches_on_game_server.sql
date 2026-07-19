-- Launch tournament matches through the same authoritative game server as
-- ordinary matches. Tournament entry fees/prizes are handled by the tournament
-- escrow, so the generated game has no per-match wallet stake.

DO $$
BEGIN
  IF to_regprocedure('public.settle_game_wallets_financial(uuid)') IS NULL THEN
    ALTER FUNCTION public.settle_game_wallets(uuid)
      RENAME TO settle_game_wallets_financial;
  END IF;
END;
$$;

-- Keep the existing financial settlement intact, but bypass it only for a
-- zero-stake game that is bound in both directions to a real tournament match.
CREATE OR REPLACE FUNCTION public.settle_game_wallets(p_game_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_is_zero_stake_tournament boolean := false;
BEGIN
  SELECT EXISTS (
    SELECT 1
      FROM public.games g
      JOIN public.tournament_matches tm
        ON tm.id = g.tournament_match_id
       AND tm.game_id = g.id
     WHERE g.id = p_game_id
       AND COALESCE(g.is_tournament, false)
       AND COALESCE(g.bet_amount, 0) = 0
       AND g.player1_id = tm.player1_id
       AND g.player2_id = tm.player2_id
  )
  INTO v_is_zero_stake_tournament;

  IF v_is_zero_stake_tournament THEN
    RETURN;
  END IF;

  PERFORM public.settle_game_wallets_financial(p_game_id);
END;
$$;

REVOKE ALL ON FUNCTION public.settle_game_wallets_financial(uuid) FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.settle_game_wallets(uuid) FROM PUBLIC, anon, authenticated;

CREATE OR REPLACE FUNCTION public.tournament_join_match(p_match_id uuid)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_uid uuid := auth.uid();
  v_match public.tournament_matches%rowtype;
  v_game_id uuid;
  v_game_type public.game_type;
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'unauthenticated' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO v_match
    FROM public.tournament_matches
   WHERE id = p_match_id
   FOR UPDATE;

  IF NOT FOUND THEN
    RAISE EXCEPTION 'match_not_found' USING ERRCODE = 'P0002';
  END IF;
  IF v_uid NOT IN (v_match.player1_id, v_match.player2_id) THEN
    RAISE EXCEPTION 'not_a_participant' USING ERRCODE = '42501';
  END IF;
  IF v_match.player1_id IS NULL OR v_match.player2_id IS NULL THEN
    RAISE EXCEPTION 'opponent_missing' USING ERRCODE = '23514';
  END IF;
  IF v_match.status IN ('completed', 'walkover', 'cancelled') THEN
    RETURN jsonb_build_object(
      'success', true,
      'status', v_match.status,
      'game_id', v_match.game_id
    );
  END IF;
  IF v_match.status NOT IN ('ready', 'in_progress') THEN
    RAISE EXCEPTION 'match_not_ready' USING ERRCODE = '23514';
  END IF;

  IF v_uid = v_match.player1_id THEN
    UPDATE public.tournament_matches
       SET player1_joined_at = COALESCE(player1_joined_at, now()),
           updated_at = now()
     WHERE id = p_match_id;
  ELSE
    UPDATE public.tournament_matches
       SET player2_joined_at = COALESCE(player2_joined_at, now()),
           updated_at = now()
     WHERE id = p_match_id;
  END IF;

  SELECT * INTO v_match
    FROM public.tournament_matches
   WHERE id = p_match_id
   FOR UPDATE;

  IF v_match.game_id IS NOT NULL THEN
    RETURN jsonb_build_object(
      'success', true,
      'status', v_match.status,
      'game_id', v_match.game_id,
      'both_joined', v_match.player1_joined_at IS NOT NULL
                     AND v_match.player2_joined_at IS NOT NULL
    );
  END IF;

  IF v_match.player1_joined_at IS NULL OR v_match.player2_joined_at IS NULL THEN
    RETURN jsonb_build_object(
      'success', true,
      'status', 'waiting_for_opponent',
      'game_id', NULL,
      'both_joined', false
    );
  END IF;

  SELECT t.game_type::public.game_type
    INTO v_game_type
    FROM public.tournaments t
   WHERE t.id = v_match.tournament_id
     AND t.status = 'in_progress'
   FOR SHARE;

  IF v_game_type IS NULL THEN
    RAISE EXCEPTION 'tournament_not_in_progress' USING ERRCODE = '23514';
  END IF;

  -- Trusted only for this transaction. The game is inserted directly as
  -- in_progress so the ordinary per-match escrow trigger is not invoked.
  PERFORM set_config('app.trusted_game_write', '1', true);

  INSERT INTO public.games (
    game_type,
    player1_id,
    player2_id,
    bet_amount,
    is_sandbox,
    status,
    started_at,
    current_turn_player_id,
    turn_started_at,
    player1_bet_amount,
    player2_bet_amount,
    player1_is_ready,
    player2_is_ready,
    pregame_started_at,
    tournament_match_id,
    is_tournament,
    game_settings
  ) VALUES (
    v_game_type,
    v_match.player1_id,
    v_match.player2_id,
    0,
    true,
    'in_progress',
    now(),
    v_match.player1_id,
    now(),
    0,
    0,
    true,
    true,
    now(),
    v_match.id,
    true,
    jsonb_build_object(
      'tournament_id', v_match.tournament_id,
      'tournament_match_id', v_match.id,
      'wallet_settlement', false
    )
  )
  RETURNING id INTO v_game_id;

  UPDATE public.tournament_matches
     SET game_id = v_game_id,
         status = 'in_progress',
         played_at = COALESCE(played_at, now()),
         updated_at = now()
   WHERE id = v_match.id;

  PERFORM set_config('app.trusted_game_write', '', true);

  RETURN jsonb_build_object(
    'success', true,
    'status', 'in_progress',
    'game_id', v_game_id,
    'game_type', v_game_type::text,
    'both_joined', true
  );
EXCEPTION
  WHEN OTHERS THEN
    PERFORM set_config('app.trusted_game_write', '', true);
    RAISE;
END;
$$;

REVOKE ALL ON FUNCTION public.tournament_join_match(uuid) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.tournament_join_match(uuid) TO authenticated;

