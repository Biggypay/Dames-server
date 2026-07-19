-- Durable, server-only state for authoritative real-time matches.
-- This lets one Render instance recover the exact board after a restart.
CREATE SCHEMA IF NOT EXISTS private;

CREATE TABLE IF NOT EXISTS private.game_server_room_states (
  game_type text NOT NULL CHECK (game_type IN ('dames', 'tictactoe', 'quoridor', 'penalty', 'chifoumi')),
  room_id text NOT NULL CHECK (room_id ~ '^[A-Za-z0-9_:.-]{1,100}$'),
  game_id uuid NOT NULL REFERENCES public.games(id) ON DELETE CASCADE,
  status text NOT NULL CHECK (status IN ('waiting', 'playing', 'paused', 'finished')),
  state jsonb NOT NULL CHECK (jsonb_typeof(state) = 'object' AND pg_column_size(state) <= 262144),
  updated_at timestamptz NOT NULL DEFAULT now(),
  PRIMARY KEY (game_type, room_id),
  UNIQUE (game_id)
);

REVOKE ALL ON SCHEMA private FROM PUBLIC, anon, authenticated;
REVOKE ALL ON TABLE private.game_server_room_states FROM PUBLIC, anon, authenticated;

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

    IF item_game_type NOT IN ('dames', 'tictactoe', 'quoridor', 'penalty', 'chifoumi')
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

CREATE OR REPLACE FUNCTION public.load_game_server_room_states()
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = pg_catalog, public, private
AS $$
DECLARE
  result jsonb;
BEGIN
  DELETE FROM private.game_server_room_states AS saved
  USING public.games AS game
  WHERE game.id = saved.game_id
    AND game.status::text IN ('completed', 'cancelled', 'abandoned');

  SELECT COALESCE(
    jsonb_agg(
      jsonb_build_object(
        'game_type', saved.game_type,
        'room_id', saved.room_id,
        'game_id', saved.game_id,
        'status', saved.status,
        'state', saved.state,
        'db_status', game.status::text
      ) ORDER BY saved.updated_at
    ),
    '[]'::jsonb
  )
  INTO result
  FROM private.game_server_room_states AS saved
  JOIN public.games AS game ON game.id = saved.game_id
  WHERE game.status::text IN ('waiting', 'in_progress');

  RETURN result;
END;
$$;

CREATE OR REPLACE FUNCTION public.delete_game_server_room_state(p_game_type text, p_room_id text)
RETURNS void
LANGUAGE sql
SECURITY DEFINER
SET search_path = pg_catalog, public, private
AS $$
  DELETE FROM private.game_server_room_states
  WHERE game_type = p_game_type AND room_id = p_room_id;
$$;

REVOKE ALL ON FUNCTION public.save_game_server_room_states(jsonb) FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.load_game_server_room_states() FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.delete_game_server_room_state(text, text) FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.save_game_server_room_states(jsonb) TO service_role;
GRANT EXECUTE ON FUNCTION public.load_game_server_room_states() TO service_role;
GRANT EXECUTE ON FUNCTION public.delete_game_server_room_state(text, text) TO service_role;
