-- Persist authoritative two-player Ludo rooms through Render restarts.
-- The public games enum already contains `ludo`; this only extends the
-- private server-state whitelist and its service-role RPC.

ALTER TABLE private.game_server_room_states
  DROP CONSTRAINT IF EXISTS game_server_room_states_game_type_check;

ALTER TABLE private.game_server_room_states
  ADD CONSTRAINT game_server_room_states_game_type_check
  CHECK (game_type IN ('dames', 'tictactoe', 'quoridor', 'penalty', 'chifoumi', 'echecs', 'ludo'));

CREATE OR REPLACE FUNCTION public.save_game_server_room_states(p_rooms jsonb)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = pg_catalog, public, private
AS $$
DECLARE
  item jsonb;
  item_game_type text;
  item_room_id text;
  item_game_id uuid;
  item_status text;
  item_state jsonb;
  database_game_type text;
  expected_database_type text;
BEGIN
  IF jsonb_typeof(p_rooms) <> 'array' OR jsonb_array_length(p_rooms) > 500 THEN
    RAISE EXCEPTION 'invalid room state batch' USING ERRCODE = '22023';
  END IF;

  FOR item IN SELECT value FROM jsonb_array_elements(p_rooms)
  LOOP
    item_game_type := item->>'game_type';
    item_room_id := item->>'room_id';
    item_status := item->>'status';
    item_state := item->'state';
    BEGIN
      item_game_id := (item->>'game_id')::uuid;
    EXCEPTION WHEN invalid_text_representation THEN
      RAISE EXCEPTION 'invalid game id' USING ERRCODE = '22023';
    END;

    IF item_game_type NOT IN ('dames', 'tictactoe', 'quoridor', 'penalty', 'chifoumi', 'echecs', 'ludo')
       OR item_room_id IS NULL OR item_room_id !~ '^[A-Za-z0-9_:.-]{1,100}$'
       OR item_status NOT IN ('waiting', 'playing', 'paused', 'finished')
       OR jsonb_typeof(item_state) <> 'object'
       OR pg_column_size(item_state) > 262144 THEN
      RAISE EXCEPTION 'invalid room state' USING ERRCODE = '22023';
    END IF;

    expected_database_type := CASE item_game_type
      WHEN 'dames' THEN 'checkers'
      WHEN 'tictactoe' THEN 'tictactoe'
      WHEN 'quoridor' THEN 'quoridor'
      WHEN 'penalty' THEN 'penalty_shootout'
      WHEN 'chifoumi' THEN 'rock_paper_scissors'
      WHEN 'echecs' THEN 'chess'
      WHEN 'ludo' THEN 'ludo'
    END;
    SELECT g.game_type::text INTO database_game_type
    FROM public.games AS g
    WHERE g.id = item_game_id;
    IF database_game_type IS NULL OR database_game_type <> expected_database_type THEN
      RAISE EXCEPTION 'room state does not match database game' USING ERRCODE = '22023';
    END IF;

    INSERT INTO private.game_server_room_states AS saved
      (game_type, room_id, game_id, status, state, updated_at)
    VALUES
      (item_game_type, item_room_id, item_game_id, item_status, item_state, now())
    ON CONFLICT (game_type, room_id) DO UPDATE
    SET game_id = EXCLUDED.game_id,
        status = EXCLUDED.status,
        state = EXCLUDED.state,
        updated_at = now();
  END LOOP;
END;
$$;

REVOKE ALL ON FUNCTION public.save_game_server_room_states(jsonb) FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.save_game_server_room_states(jsonb) TO service_role;
