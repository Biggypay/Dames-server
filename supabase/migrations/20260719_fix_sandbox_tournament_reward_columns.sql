-- The tournament stores prizes in rewards JSON ({first, second}); keep the
-- sandbox payout trigger aligned with the real schema. No third prize exists.
CREATE OR REPLACE FUNCTION public.pay_sandbox_tournament_prizes()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_mode text;
  v_enabled boolean;
  v_runner_up uuid;
  v_before numeric;
  v_amount numeric;
  v_rank integer;
  v_user uuid;
BEGIN
  IF NEW.status <> 'completed' OR OLD.status='completed' OR NEW.winner_id IS NULL THEN RETURN NEW; END IF;
  SELECT trim(both '"' from value::text) INTO v_mode FROM public.platform_settings WHERE key='payment_mode';
  SELECT COALESCE(NULLIF(trim(both '"' from value),'')::boolean,false) INTO v_enabled
  FROM public.platform_settings WHERE key='sandbox_tournament_auto_payout';
  IF v_mode IS DISTINCT FROM 'sandbox' OR NOT COALESCE(v_enabled,false) THEN RETURN NEW; END IF;

  SELECT CASE WHEN player1_id=NEW.winner_id THEN player2_id ELSE player1_id END
  INTO v_runner_up FROM public.tournament_matches
  WHERE tournament_id=NEW.id AND round='final' AND status='completed'
  ORDER BY played_at DESC NULLS LAST, updated_at DESC LIMIT 1;

  FOR v_rank,v_user,v_amount IN
    SELECT * FROM (VALUES
      (1,NEW.winner_id,COALESCE(NULLIF(NEW.rewards->>'first','')::numeric,0)),
      (2,v_runner_up,COALESCE(NULLIF(NEW.rewards->>'second','')::numeric,0))
    ) p(rank_no,user_id,amount)
  LOOP
    IF v_user IS NULL OR v_amount<=0 OR EXISTS(
      SELECT 1 FROM public.transactions
      WHERE type='tournament_prize' AND is_sandbox=true
        AND metadata->>'tournament_id'=NEW.id::text
        AND metadata->>'rank'=v_rank::text
    ) THEN CONTINUE; END IF;

    SELECT sandbox_balance INTO v_before FROM public.wallets WHERE user_id=v_user FOR UPDATE;
    IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
    v_before:=COALESCE(v_before,0);
    UPDATE public.wallets SET sandbox_balance=v_before+v_amount,updated_at=now() WHERE user_id=v_user;
    INSERT INTO public.transactions
      (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
    VALUES
      (v_user,'tournament_prize',v_amount,v_before,v_before+v_amount,true,
       CASE WHEN v_rank=1 THEN 'Premier prix tournoi (sandbox)' ELSE 'Deuxieme prix tournoi (sandbox)' END,
       jsonb_build_object('tournament_id',NEW.id,'rank',v_rank,'payout_mode','sandbox','escrow',true));
  END LOOP;

  DELETE FROM public.notifications
  WHERE data->>'kind'='tournament_manual_payout' AND data->>'tournament_id'=NEW.id::text;
  RETURN NEW;
END;
$$;

REVOKE ALL ON FUNCTION public.pay_sandbox_tournament_prizes() FROM PUBLIC, anon, authenticated;
