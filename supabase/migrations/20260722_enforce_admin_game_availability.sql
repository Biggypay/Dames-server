-- Make the administrator's global game switches authoritative at the database
-- boundary. Existing in-progress games are never interrupted, but no new game
-- can be created or moved to in_progress while globally locked/disabled.

CREATE OR REPLACE FUNCTION public.enforce_admin_game_availability()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = pg_catalog, public
AS $$
DECLARE
  locked_value text;
  disabled_value text;
  disabled_games jsonb := '[]'::jsonb;
  game_key text := NEW.game_type::text;
  game_alias text;
BEGIN
  -- Do not retroactively terminate or mutate a match that already started.
  IF TG_OP = 'UPDATE'
     AND OLD.status::text = 'in_progress'
     AND NEW.status::text = 'in_progress' THEN
    RETURN NEW;
  END IF;

  SELECT value INTO locked_value
  FROM public.platform_settings
  WHERE key = 'games_locked';

  IF lower(COALESCE(trim(locked_value), 'false')) IN ('true', '1', 'yes', 'on') THEN
    RAISE EXCEPTION 'games_globally_locked' USING ERRCODE = 'check_violation';
  END IF;

  SELECT value INTO disabled_value
  FROM public.platform_settings
  WHERE key = 'disabled_games';

  BEGIN
    disabled_games := COALESCE(NULLIF(disabled_value, ''), '[]')::jsonb;
    IF jsonb_typeof(disabled_games) <> 'array' THEN disabled_games := '[]'::jsonb; END IF;
  EXCEPTION WHEN OTHERS THEN
    disabled_games := '[]'::jsonb;
  END;

  game_alias := CASE game_key
    WHEN 'checkers' THEN 'dames'
    WHEN 'tictactoe' THEN 'ttt'
    WHEN 'rock_paper_scissors' THEN 'chifoumi'
    WHEN 'penalty_shootout' THEN 'penalty'
    WHEN 'chess' THEN 'echecs'
    ELSE game_key
  END;

  IF disabled_games ? game_key OR disabled_games ? game_alias THEN
    RAISE EXCEPTION 'game_disabled_by_administrator' USING ERRCODE = 'check_violation';
  END IF;

  RETURN NEW;
END;
$$;

DROP TRIGGER IF EXISTS enforce_admin_game_availability_trigger ON public.games;
CREATE TRIGGER enforce_admin_game_availability_trigger
BEFORE INSERT OR UPDATE OF status, game_type ON public.games
FOR EACH ROW
WHEN (NEW.status::text IN ('waiting', 'in_progress'))
EXECUTE FUNCTION public.enforce_admin_game_availability();

REVOKE ALL ON FUNCTION public.enforce_admin_game_availability() FROM PUBLIC, anon, authenticated;
