-- Allow authenticated spectators to view ALL live matches, including sandbox
-- games. The previous "Authenticated can view live public matches" policy
-- required is_sandbox = false, so sandbox matches (the vast majority of live
-- play) never surfaced in the spectator "live matches" feed, which always
-- showed "Aucun match en direct". Per product decision, every live 2-player
-- match should be watchable/bettable.
DROP POLICY IF EXISTS "Authenticated can view live public matches" ON public.games;
CREATE POLICY "Authenticated can view live public matches"
ON public.games FOR SELECT TO authenticated
USING (
  status = 'in_progress'::public.game_status
  AND is_ai_opponent = false
  AND player2_id IS NOT NULL
);
