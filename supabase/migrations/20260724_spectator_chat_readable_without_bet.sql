-- Watchers could send a spectator message but could not READ the live chat
-- unless they were a player or had already placed a bet, so people who did not
-- bet could not really take part in the live betting chat. Let any authenticated
-- user read the spectator chat of a real (non-AI, 2-player) match. Inserting a
-- message is already limited to the author (auth.uid() = user_id).
DROP POLICY IF EXISTS "Participants and spectators can view spectator messages" ON public.spectator_messages;
CREATE POLICY "Anyone can view spectator messages of live matches"
ON public.spectator_messages FOR SELECT TO authenticated
USING (
  EXISTS (
    SELECT 1 FROM public.games g
    WHERE g.id = spectator_messages.game_id
      AND g.is_ai_opponent = false
      AND g.player2_id IS NOT NULL
  )
);
