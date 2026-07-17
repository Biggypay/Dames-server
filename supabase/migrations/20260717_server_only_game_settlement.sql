-- Apply only after the matching server release is live with
-- SUPABASE_SERVICE_ROLE_KEY configured in Render.
-- Browser sessions must never be able to decide a winner or settle a wallet.

REVOKE ALL ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) FROM PUBLIC;
REVOKE ALL ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) FROM anon;
REVOKE ALL ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) FROM authenticated;
GRANT EXECUTE ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) TO service_role;

