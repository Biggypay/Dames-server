-- A player may voluntarily lose their own active game, but must never be able
-- to select the winner. The previous RPC delegated to submit_game_result(),
-- whose service_role check correctly rejected authenticated browser calls.
-- These narrowly-scoped RPCs validate the caller and perform the same trusted,
-- atomic completion used by the server; completion triggers remain responsible
-- for escrow settlement, history and tournament advancement.

CREATE OR REPLACE FUNCTION public.forfeit_active_game(p_game_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_uid uuid := auth.uid();
  g public.games%ROWTYPE;
  v_winner_id uuid;
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO g
  FROM public.games
  WHERE id = p_game_id
  FOR UPDATE;

  IF g.id IS NULL OR g.status <> 'in_progress'::public.game_status THEN
    RAISE EXCEPTION 'active game not found' USING ERRCODE = 'P0002';
  END IF;

  IF g.player1_id = v_uid THEN
    v_winner_id := g.player2_id;
  ELSIF g.player2_id = v_uid THEN
    v_winner_id := g.player1_id;
  ELSE
    RAISE EXCEPTION 'not a participant' USING ERRCODE = '42501';
  END IF;

  IF v_winner_id IS NULL THEN
    RAISE EXCEPTION 'opponent is missing' USING ERRCODE = '22023';
  END IF;

  PERFORM set_config('app.trusted_game_write', '1', true);
  UPDATE public.games
  SET status = 'completed'::public.game_status,
      result = 'timeout'::public.game_result,
      winner_id = v_winner_id,
      duration_seconds = GREATEST(
        0,
        FLOOR(EXTRACT(EPOCH FROM (now() - COALESCE(g.started_at, g.created_at))))::integer
      ),
      completed_at = now(),
      updated_at = now()
  WHERE id = g.id
    AND status = 'in_progress'::public.game_status;
  PERFORM set_config('app.trusted_game_write', '', true);

  IF NOT FOUND THEN
    RAISE EXCEPTION 'game was already settled or changed state' USING ERRCODE = 'P0001';
  END IF;
EXCEPTION WHEN OTHERS THEN
  PERFORM set_config('app.trusted_game_write', '', true);
  RAISE;
END;
$function$;

CREATE OR REPLACE FUNCTION public.resolve_disconnected_opponent(p_game_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_uid uuid := auth.uid();
  g public.games%ROWTYPE;
  v_my_seen_at timestamptz;
  v_opponent_seen_at timestamptz;
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO g
  FROM public.games
  WHERE id = p_game_id
  FOR UPDATE;

  IF g.id IS NULL OR g.status <> 'in_progress'::public.game_status THEN
    RAISE EXCEPTION 'active game not found' USING ERRCODE = 'P0002';
  END IF;

  IF g.player1_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  ELSIF g.player2_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  ELSE
    RAISE EXCEPTION 'not a participant' USING ERRCODE = '42501';
  END IF;

  IF v_my_seen_at < now() - interval '15 seconds' THEN
    RAISE EXCEPTION 'caller must still be connected' USING ERRCODE = '42501';
  END IF;

  IF v_opponent_seen_at + interval '75 seconds' > now() THEN
    RAISE EXCEPTION 'opponent reconnect time has not expired' USING ERRCODE = '22023';
  END IF;

  PERFORM set_config('app.trusted_game_write', '1', true);
  UPDATE public.games
  SET status = 'completed'::public.game_status,
      result = 'timeout'::public.game_result,
      winner_id = v_uid,
      duration_seconds = GREATEST(
        0,
        FLOOR(EXTRACT(EPOCH FROM (now() - COALESCE(g.started_at, g.created_at))))::integer
      ),
      completed_at = now(),
      updated_at = now()
  WHERE id = g.id
    AND status = 'in_progress'::public.game_status;
  PERFORM set_config('app.trusted_game_write', '', true);

  IF NOT FOUND THEN
    RAISE EXCEPTION 'game was already settled or changed state' USING ERRCODE = 'P0001';
  END IF;
EXCEPTION WHEN OTHERS THEN
  PERFORM set_config('app.trusted_game_write', '', true);
  RAISE;
END;
$function$;

REVOKE ALL ON FUNCTION public.forfeit_active_game(uuid) FROM PUBLIC, anon;
REVOKE ALL ON FUNCTION public.resolve_disconnected_opponent(uuid) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.forfeit_active_game(uuid) TO authenticated;
GRANT EXECUTE ON FUNCTION public.resolve_disconnected_opponent(uuid) TO authenticated;
