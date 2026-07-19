-- Keep the landing Top 10 public without a SECURITY DEFINER view. A small RLS
-- protected cache exposes only display-safe ranking fields and is refreshed by
-- trusted triggers whenever statistics or public profile fields change.

BEGIN;

DROP VIEW public.public_leaderboard;

CREATE TABLE public.public_leaderboard (
  rank bigint NOT NULL,
  username text NOT NULL,
  avatar_url text,
  wins integer NOT NULL,
  total_games integer NOT NULL,
  win_rate numeric NOT NULL,
  xp integer NOT NULL,
  division text,
  stage text,
  ranking_score numeric NOT NULL
);

CREATE INDEX public_leaderboard_rank_idx ON public.public_leaderboard(rank);
ALTER TABLE public.public_leaderboard ENABLE ROW LEVEL SECURITY;

CREATE POLICY "Public can read leaderboard"
ON public.public_leaderboard FOR SELECT
TO anon, authenticated
USING (true);

REVOKE ALL ON public.public_leaderboard FROM PUBLIC, anon, authenticated;
GRANT SELECT ON public.public_leaderboard TO anon, authenticated, service_role;

CREATE OR REPLACE FUNCTION public.refresh_public_leaderboard()
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
BEGIN
  TRUNCATE TABLE public.public_leaderboard;
  INSERT INTO public.public_leaderboard
    (rank,username,avatar_url,wins,total_games,win_rate,xp,division,stage,ranking_score)
  SELECT
    dense_rank() OVER (
      ORDER BY gs.wins DESC,
        CASE WHEN gs.total_games>0 THEN gs.wins::numeric/gs.total_games ELSE 0 END DESC,
        gs.longest_win_streak DESC,
        gs.xp DESC
    ),
    p.username,
    p.avatar_url,
    gs.wins,
    gs.total_games,
    CASE WHEN gs.total_games>0 THEN round(gs.wins::numeric/gs.total_games*100,1) ELSE 0 END,
    gs.xp,
    gs.division,
    gs.stage,
    gs.wins::numeric
  FROM public.game_statistics gs
  JOIN public.profiles p ON p.id=gs.user_id
  WHERE gs.total_games>0 OR gs.xp>0
  ORDER BY 1
  LIMIT 100;
  RETURN;
END;
$$;

CREATE OR REPLACE FUNCTION public.trigger_refresh_public_leaderboard()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
BEGIN
  PERFORM public.refresh_public_leaderboard();
  RETURN NULL;
END;
$$;

DROP TRIGGER IF EXISTS refresh_public_leaderboard_from_stats ON public.game_statistics;
CREATE TRIGGER refresh_public_leaderboard_from_stats
AFTER INSERT OR UPDATE OR DELETE ON public.game_statistics
FOR EACH STATEMENT EXECUTE FUNCTION public.trigger_refresh_public_leaderboard();

DROP TRIGGER IF EXISTS refresh_public_leaderboard_from_profiles ON public.profiles;
CREATE TRIGGER refresh_public_leaderboard_from_profiles
AFTER INSERT OR UPDATE OF username,avatar_url OR DELETE ON public.profiles
FOR EACH STATEMENT EXECUTE FUNCTION public.trigger_refresh_public_leaderboard();

SELECT public.refresh_public_leaderboard();

REVOKE ALL ON FUNCTION public.refresh_public_leaderboard() FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.trigger_refresh_public_leaderboard() FROM PUBLIC, anon, authenticated;

COMMIT;
