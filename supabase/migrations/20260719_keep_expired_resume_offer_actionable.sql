-- Never hide an expired resume offer while the database game is still active.
-- The player must retain a safe way to resume or voluntarily forfeit; the game
-- server remains the authority and Supabase does not silently choose a winner.

CREATE OR REPLACE FUNCTION public.get_game_resume_offer(p_game_id uuid DEFAULT NULL)
RETURNS TABLE(
  game_id uuid,
  game_type text,
  bet_amount numeric,
  opponent_id uuid,
  reconnect_deadline_at timestamptz,
  server_now timestamptz,
  seconds_remaining integer,
  opponent_waiting boolean,
  both_players_disconnected boolean
)
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_uid uuid := auth.uid();
  g public.games%ROWTYPE;
  v_my_seen_at timestamptz;
  v_opponent_seen_at timestamptz;
  v_deadline timestamptz;
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;

  SELECT *
  INTO g
  FROM public.games
  WHERE status = 'in_progress'::public.game_status
    AND is_ai_opponent = false
    AND player1_id IS NOT NULL
    AND player2_id IS NOT NULL
    AND (p_game_id IS NULL OR id = p_game_id)
    AND (player1_id = v_uid OR player2_id = v_uid)
  ORDER BY COALESCE(last_move_at, updated_at, created_at) DESC
  LIMIT 1;

  IF g.id IS NULL THEN
    RETURN;
  END IF;

  IF g.player1_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  ELSE
    v_my_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  END IF;

  v_deadline := v_my_seen_at + interval '75 seconds';

  RETURN QUERY
  SELECT
    g.id,
    g.game_type::text,
    g.bet_amount,
    CASE WHEN g.player1_id = v_uid THEN g.player2_id ELSE g.player1_id END,
    v_deadline,
    now(),
    GREATEST(0, FLOOR(EXTRACT(EPOCH FROM (v_deadline - now())))::integer),
    v_opponent_seen_at >= now() - interval '15 seconds',
    v_my_seen_at < now() - interval '15 seconds'
      AND v_opponent_seen_at < now() - interval '15 seconds';
END;
$function$;

REVOKE ALL ON FUNCTION public.get_game_resume_offer(uuid) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.get_game_resume_offer(uuid) TO authenticated;
