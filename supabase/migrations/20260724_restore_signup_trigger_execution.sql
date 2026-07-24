-- Fix: no user could receive a confirmation / OTP code when signing up.
--
-- 20260719_restrict_trigger_function_execution.sql revoked EXECUTE on every
-- SECURITY DEFINER trigger function in `public` from PUBLIC (and anon,
-- authenticated) to shrink the SECURITY DEFINER surface. That is the right call
-- for functions reachable from the API, but it also stripped the grant the
-- Supabase Auth server depends on.
--
-- On sign-up, GoTrue inserts into `auth.users` while connected as the
-- `supabase_auth_admin` role. The AFTER INSERT trigger on that table (the
-- standard `public.handle_new_user`, and any sibling auth triggers) is a
-- SECURITY DEFINER function whose EXECUTE privilege `supabase_auth_admin` held
-- only through PUBLIC. With that grant revoked, PostgreSQL refuses to fire the
-- trigger, the INSERT rolls back, and GoTrue returns "Database error saving new
-- user". Because the account is never created, no confirmation / OTP code is
-- ever issued or emailed.
--
-- Restore sign-up by re-granting EXECUTE to `supabase_auth_admin` for the
-- trigger functions that are actually attached to triggers on tables in the
-- `auth` schema. This is scoped to the auth role only, so the functions stay
-- hidden from anon / authenticated and the original hardening is preserved.
DO $$
DECLARE
  fn record;
BEGIN
  FOR fn IN
    SELECT DISTINCT p.oid::regprocedure AS signature
    FROM pg_trigger AS t
    JOIN pg_class AS c ON c.oid = t.tgrelid
    JOIN pg_namespace AS cn ON cn.oid = c.relnamespace
    JOIN pg_proc AS p ON p.oid = t.tgfoid
    JOIN pg_namespace AS pn ON pn.oid = p.pronamespace
    WHERE cn.nspname = 'auth'
      AND pn.nspname = 'public'
      AND NOT t.tgisinternal
  LOOP
    EXECUTE format('GRANT EXECUTE ON FUNCTION %s TO supabase_auth_admin', fn.signature);
  END LOOP;
END;
$$;
