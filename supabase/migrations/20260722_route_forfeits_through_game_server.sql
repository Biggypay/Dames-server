-- Paid-game outcomes must be chosen and settled by the authoritative game
-- server. The web client now calls POST /game/resign with a signed server JWT.
-- Keeping this older RPC executable by players would leave a second outcome
-- path that can diverge from the persisted room and escrow state.
REVOKE ALL ON FUNCTION public.forfeit_active_game(uuid) FROM PUBLIC;
REVOKE EXECUTE ON FUNCTION public.forfeit_active_game(uuid) FROM anon, authenticated;
GRANT EXECUTE ON FUNCTION public.forfeit_active_game(uuid) TO service_role;
