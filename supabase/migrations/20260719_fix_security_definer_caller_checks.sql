-- In a SECURITY DEFINER function, current_user is the function owner. It must
-- never be used to identify the API caller. Preserve elevated execution while
-- checking the JWT role/user supplied by PostgREST.
DO $$
DECLARE
  signature regprocedure;
  definition text;
BEGIN
  FOREACH signature IN ARRAY ARRAY[
    'public.flag_support_escalation(uuid,text,uuid)'::regprocedure,
    'public.get_pending_support_conversations()'::regprocedure,
    'public.send_support_reply(uuid,text,uuid)'::regprocedure
  ]
  LOOP
    SELECT pg_get_functiondef(signature) INTO definition;
    definition := replace(
      definition,
      'IF current_user NOT IN (''postgres'',''service_role'',''supabase_admin'') THEN',
      'IF auth.role() <> ''service_role'' AND NOT public.has_role(auth.uid(), ''admin''::public.app_role) THEN'
    );
    EXECUTE definition;
  END LOOP;

  SELECT pg_get_functiondef('public.update_engagement_stats(uuid)'::regprocedure) INTO definition;
  definition := replace(
    definition,
    'IF current_user NOT IN (''postgres'',''service_role'',''supabase_admin'') THEN',
    'IF auth.role() <> ''service_role'' THEN'
  );
  EXECUTE definition;

  SELECT pg_get_functiondef('public.submit_game_result(uuid,text,text,uuid,numeric,integer)'::regprocedure) INTO definition;
  definition := replace(
    definition,
    'IF current_user NOT IN (''postgres'', ''service_role'', ''supabase_admin'') THEN',
    'IF auth.role() <> ''service_role'' THEN'
  );
  EXECUTE definition;
END;
$$;

-- Restore the intended API surface after CREATE OR REPLACE.
REVOKE ALL ON FUNCTION public.flag_support_escalation(uuid, text, uuid) FROM PUBLIC, anon;
REVOKE ALL ON FUNCTION public.get_pending_support_conversations() FROM PUBLIC, anon;
REVOKE ALL ON FUNCTION public.send_support_reply(uuid, text, uuid) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.flag_support_escalation(uuid, text, uuid) TO authenticated, service_role;
GRANT EXECUTE ON FUNCTION public.get_pending_support_conversations() TO authenticated, service_role;
GRANT EXECUTE ON FUNCTION public.send_support_reply(uuid, text, uuid) TO authenticated, service_role;

REVOKE ALL ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.submit_game_result(uuid, text, text, uuid, numeric, integer) TO service_role;
