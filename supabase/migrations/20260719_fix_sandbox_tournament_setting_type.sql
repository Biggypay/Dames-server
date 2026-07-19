-- platform_settings.value is text in this project, not jsonb.
DO $$
DECLARE
  v_definition text;
BEGIN
  SELECT pg_get_functiondef('public.pay_sandbox_tournament_prizes()'::regprocedure)
  INTO v_definition;
  v_definition := replace(
    v_definition,
    'COALESCE((value #>> ''{}'')::boolean,false)',
    'COALESCE(NULLIF(trim(both ''"'' from value),'''')::boolean,false)'
  );
  IF position('value #>>' IN v_definition) > 0 THEN
    RAISE EXCEPTION 'Unexpected tournament payout setting expression';
  END IF;
  EXECUTE v_definition;
END;
$$;

REVOKE ALL ON FUNCTION public.pay_sandbox_tournament_prizes() FROM PUBLIC, anon, authenticated;
