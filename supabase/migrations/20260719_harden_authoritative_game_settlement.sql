-- The game server is the only authority allowed to settle a real-time match.
-- A row must have reached in_progress first, and it can be settled exactly once.
CREATE OR REPLACE FUNCTION public.submit_game_result(
  p_game_id uuid,
  p_status text,
  p_result text DEFAULT NULL,
  p_winner_id uuid DEFAULT NULL,
  p_platform_fee numeric DEFAULT NULL,
  p_duration_seconds integer DEFAULT NULL
)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public
AS $$
DECLARE
  g public.games%ROWTYPE;
BEGIN
  IF current_user NOT IN ('postgres', 'service_role', 'supabase_admin') THEN
    RAISE EXCEPTION 'server settlement required' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO g FROM public.games WHERE id = p_game_id FOR UPDATE;
  IF g.id IS NULL THEN RAISE EXCEPTION 'game not found' USING ERRCODE = 'P0002'; END IF;

  -- Duplicate server deliveries are safe because the wallet pipeline is idempotent.
  IF g.status = 'completed'::game_status THEN
    PERFORM public.record_completed_game(p_game_id);
    RETURN;
  END IF;
  IF g.status <> 'in_progress'::game_status THEN
    RAISE EXCEPTION 'game is not in progress' USING ERRCODE = 'P0001';
  END IF;
  IF p_status <> 'completed' OR p_result IS NULL THEN
    RAISE EXCEPTION 'a settlement must complete the game with a result' USING ERRCODE = '22023';
  END IF;
  IF p_result NOT IN ('win', 'timeout', 'draw', 'mutual_quit') THEN
    RAISE EXCEPTION 'invalid final result' USING ERRCODE = '22023';
  END IF;
  IF p_winner_id IS NOT NULL AND p_winner_id <> g.player1_id AND p_winner_id <> g.player2_id THEN
    RAISE EXCEPTION 'winner must be a participant' USING ERRCODE = '22023';
  END IF;
  IF p_result IN ('win', 'timeout') AND p_winner_id IS NULL THEN
    RAISE EXCEPTION 'a win or timeout requires one winner' USING ERRCODE = '22023';
  END IF;
  IF p_result IN ('draw', 'mutual_quit') AND p_winner_id IS NOT NULL THEN
    RAISE EXCEPTION 'a draw or mutual quit cannot have a winner' USING ERRCODE = '22023';
  END IF;
  IF COALESCE(p_platform_fee, 0) < 0 OR COALESCE(p_platform_fee, 0) > COALESCE(g.bet_amount, 0) * 2 THEN
    RAISE EXCEPTION 'invalid platform fee' USING ERRCODE = '22023';
  END IF;

  PERFORM set_config('app.trusted_game_write', '1', true);
  UPDATE public.games
  SET status = 'completed'::game_status,
      result = p_result::game_result,
      winner_id = p_winner_id,
      platform_fee = COALESCE(p_platform_fee, platform_fee),
      duration_seconds = GREATEST(0, COALESCE(p_duration_seconds, duration_seconds, 0)),
      completed_at = now(),
      updated_at = now()
  WHERE id = p_game_id AND status = 'in_progress'::game_status;
  PERFORM set_config('app.trusted_game_write', '', true);
  IF NOT FOUND THEN RAISE EXCEPTION 'game was already settled or changed state' USING ERRCODE = 'P0001'; END IF;

  PERFORM public.record_completed_game(p_game_id);
EXCEPTION WHEN OTHERS THEN
  PERFORM set_config('app.trusted_game_write', '', true);
  RAISE;
END;
$$;

REVOKE ALL ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) TO service_role;
