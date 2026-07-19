-- Keep every financial flow server-controlled while MindSpille uses the sandbox
-- wallet. MonCash remains disabled until a dedicated payment integration exists.

BEGIN;

-- RLS does not protect TRUNCATE. Client roles never need schema-management rights.
REVOKE TRUNCATE, REFERENCES, TRIGGER ON ALL TABLES IN SCHEMA public FROM anon, authenticated;
ALTER DEFAULT PRIVILEGES IN SCHEMA public
  REVOKE TRUNCATE, REFERENCES, TRIGGER ON TABLES FROM anon, authenticated;

INSERT INTO public.platform_settings (key, value, description)
VALUES
  ('commission_percent', '10'::jsonb, 'Commission de la plateforme en pourcentage'),
  ('payment_mode', '"sandbox"'::jsonb, 'sandbox jusqu a l integration MonCash'),
  ('moncash_enabled', 'false'::jsonb, 'Activation du paiement MonCash'),
  ('sandbox_tournament_auto_payout', 'true'::jsonb, 'Versement automatique des prix de tournoi en portefeuille sandbox')
ON CONFLICT (key) DO UPDATE
SET value = EXCLUDED.value,
    description = EXCLUDED.description,
    updated_at = now();

-- This view deliberately exposes only ranking fields. The view owner reads the
-- protected source tables; visitors never receive direct access to those tables.
ALTER VIEW public.public_leaderboard
  SET (security_invoker = false, security_barrier = true);
REVOKE ALL ON public.public_leaderboard FROM PUBLIC, anon, authenticated;
GRANT SELECT ON public.public_leaderboard TO anon, authenticated, service_role;

-- Preserve the wallet mode used when an event wager is locked. Settlement must
-- never depend on a player's later sandbox/real-wallet toggle.
ALTER TABLE public.event_bets
  ADD COLUMN IF NOT EXISTS is_sandbox boolean;

UPDATE public.event_bets eb
SET is_sandbox = COALESCE(
  (
    SELECT t.is_sandbox
    FROM public.transactions t
    WHERE t.metadata->>'bet_id' = eb.id::text
    ORDER BY t.created_at ASC
    LIMIT 1
  ),
  (SELECT w.is_sandbox_mode FROM public.wallets w WHERE w.user_id = eb.user_id),
  true
)
WHERE eb.is_sandbox IS NULL;

ALTER TABLE public.event_bets
  ALTER COLUMN is_sandbox SET DEFAULT true,
  ALTER COLUMN is_sandbox SET NOT NULL;

CREATE OR REPLACE FUNCTION public.guard_event_bet_insert()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_event_status text;
  v_wallet public.wallets%ROWTYPE;
  v_before numeric;
  v_after numeric;
  v_trusted boolean := current_setting('app.trusted_event_bet_write', true) = '1';
BEGIN
  IF v_trusted OR COALESCE(auth.jwt()->>'role', '') = 'service_role' THEN
    IF NEW.status IS DISTINCT FROM 'pending' THEN RAISE EXCEPTION 'invalid_bet_status'; END IF;
    RETURN NEW;
  END IF;

  IF auth.uid() IS NULL OR NEW.user_id IS DISTINCT FROM auth.uid() THEN
    RAISE EXCEPTION 'forbidden' USING ERRCODE = '42501';
  END IF;
  IF NEW.status IS DISTINCT FROM 'pending' OR NEW.amount IS NULL OR NEW.amount <= 0
     OR NEW.bet_on NOT IN ('a','b') THEN
    RAISE EXCEPTION 'invalid_bet';
  END IF;

  SELECT status INTO v_event_status
  FROM public.events WHERE id = NEW.event_id FOR KEY SHARE;
  IF NOT FOUND THEN RAISE EXCEPTION 'event_not_found'; END IF;
  IF v_event_status <> 'live' THEN RAISE EXCEPTION 'event_not_open'; END IF;
  IF public.is_wallet_frozen(NEW.user_id) THEN RAISE EXCEPTION 'wallet_frozen'; END IF;

  SELECT * INTO v_wallet FROM public.wallets
  WHERE user_id = NEW.user_id FOR UPDATE;
  IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;

  NEW.is_sandbox := COALESCE(v_wallet.is_sandbox_mode, true);
  v_before := CASE WHEN NEW.is_sandbox
    THEN COALESCE(v_wallet.sandbox_balance, 0)
    ELSE COALESCE(v_wallet.balance, 0) END;
  IF v_before < NEW.amount THEN RAISE EXCEPTION 'insufficient_funds'; END IF;
  v_after := v_before - NEW.amount;

  IF NEW.is_sandbox THEN
    UPDATE public.wallets SET sandbox_balance = v_after, updated_at = now()
    WHERE id = v_wallet.id;
  ELSE
    UPDATE public.wallets SET balance = v_after, updated_at = now()
    WHERE id = v_wallet.id;
  END IF;

  INSERT INTO public.transactions
    (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
  VALUES
    (NEW.user_id,'bet_placed',NEW.amount,v_before,v_after,NEW.is_sandbox,
     'Pari evenement verrouille',
     jsonb_build_object('event_id',NEW.event_id,'bet_on',NEW.bet_on,'bet_id',NEW.id,'escrow',true));
  RETURN NEW;
END;
$$;

DROP TRIGGER IF EXISTS guard_event_bet_insert ON public.event_bets;
CREATE TRIGGER guard_event_bet_insert
BEFORE INSERT ON public.event_bets
FOR EACH ROW EXECUTE FUNCTION public.guard_event_bet_insert();

CREATE OR REPLACE FUNCTION public.place_event_bet(p_event_id uuid, p_bet_on text, p_amount numeric)
RETURNS uuid
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_user uuid := auth.uid();
  v_wallet public.wallets%ROWTYPE;
  v_event_status text;
  v_before numeric;
  v_after numeric;
  v_bet_id uuid := gen_random_uuid();
  v_is_sandbox boolean;
BEGIN
  IF v_user IS NULL THEN RAISE EXCEPTION 'not_authenticated' USING ERRCODE = '42501'; END IF;
  IF p_amount IS NULL OR p_amount <= 0 THEN RAISE EXCEPTION 'invalid_amount'; END IF;
  IF p_bet_on NOT IN ('a','b') THEN RAISE EXCEPTION 'invalid_bet_on'; END IF;

  SELECT status INTO v_event_status FROM public.events
  WHERE id = p_event_id FOR KEY SHARE;
  IF NOT FOUND THEN RAISE EXCEPTION 'event_not_found'; END IF;
  IF v_event_status <> 'live' THEN RAISE EXCEPTION 'event_not_open'; END IF;
  IF public.is_wallet_frozen(v_user) THEN RAISE EXCEPTION 'wallet_frozen'; END IF;

  SELECT * INTO v_wallet FROM public.wallets WHERE user_id = v_user FOR UPDATE;
  IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
  v_is_sandbox := COALESCE(v_wallet.is_sandbox_mode, true);
  v_before := CASE WHEN v_is_sandbox THEN COALESCE(v_wallet.sandbox_balance,0)
                   ELSE COALESCE(v_wallet.balance,0) END;
  IF v_before < p_amount THEN RAISE EXCEPTION 'insufficient_funds'; END IF;
  v_after := v_before - p_amount;

  IF v_is_sandbox THEN
    UPDATE public.wallets SET sandbox_balance=v_after, updated_at=now() WHERE id=v_wallet.id;
  ELSE
    UPDATE public.wallets SET balance=v_after, updated_at=now() WHERE id=v_wallet.id;
  END IF;

  PERFORM set_config('app.trusted_event_bet_write','1',true);
  INSERT INTO public.event_bets (id,event_id,user_id,bet_on,amount,status,is_sandbox)
  VALUES (v_bet_id,p_event_id,v_user,p_bet_on,p_amount,'pending',v_is_sandbox);
  PERFORM set_config('app.trusted_event_bet_write','0',true);

  INSERT INTO public.transactions
    (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
  VALUES
    (v_user,'bet_placed',p_amount,v_before,v_after,v_is_sandbox,'Pari evenement',
     jsonb_build_object('event_id',p_event_id,'bet_on',p_bet_on,'bet_id',v_bet_id,'escrow',true));
  RETURN v_bet_id;
END;
$$;

-- A match spectator may create only a clean pending offer. Acceptance remains
-- atomic through accept_match_spectator_bet(), which locks both stakes.
CREATE OR REPLACE FUNCTION public.guard_match_spectator_bet_insert()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_game public.games%ROWTYPE;
  v_wallet public.wallets%ROWTYPE;
  v_available numeric;
BEGIN
  IF COALESCE(auth.jwt()->>'role','') = 'service_role' THEN RETURN NEW; END IF;
  IF auth.uid() IS NULL OR NEW.creator_id IS DISTINCT FROM auth.uid() THEN
    RAISE EXCEPTION 'forbidden' USING ERRCODE='42501';
  END IF;
  IF NEW.amount IS NULL OR NEW.amount <= 0 OR NEW.status IS DISTINCT FROM 'pending'
     OR NEW.acceptor_id IS NOT NULL OR NEW.acceptor_bet_on IS NOT NULL
     OR NEW.winner_id IS NOT NULL OR NEW.accepted_at IS NOT NULL
     OR NEW.resolved_at IS NOT NULL OR COALESCE(NEW.stakes_locked,false) THEN
    RAISE EXCEPTION 'invalid_spectator_bet';
  END IF;

  SELECT * INTO v_game FROM public.games WHERE id=NEW.game_id FOR KEY SHARE;
  IF NOT FOUND OR v_game.status <> 'in_progress' THEN RAISE EXCEPTION 'game_not_available'; END IF;
  IF NEW.creator_bet_on NOT IN (v_game.player1_id,v_game.player2_id) THEN RAISE EXCEPTION 'invalid_bet_side'; END IF;
  IF NEW.creator_id IN (v_game.player1_id,v_game.player2_id) THEN RAISE EXCEPTION 'players_cannot_spectator_bet'; END IF;
  IF public.is_wallet_frozen(NEW.creator_id) THEN RAISE EXCEPTION 'wallet_frozen'; END IF;

  SELECT * INTO v_wallet FROM public.wallets WHERE user_id=NEW.creator_id FOR KEY SHARE;
  IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
  IF COALESCE(v_wallet.is_sandbox_mode,true) IS DISTINCT FROM COALESCE(v_game.is_sandbox,true) THEN
    RAISE EXCEPTION 'wallet_mode_mismatch';
  END IF;
  v_available := CASE WHEN v_game.is_sandbox THEN COALESCE(v_wallet.sandbox_balance,0)
                      ELSE COALESCE(v_wallet.balance,0) END;
  IF v_available < NEW.amount THEN RAISE EXCEPTION 'insufficient_funds'; END IF;
  RETURN NEW;
END;
$$;

DROP TRIGGER IF EXISTS guard_match_spectator_bet_insert ON public.spectator_bets;
CREATE TRIGGER guard_match_spectator_bet_insert
BEFORE INSERT ON public.spectator_bets
FOR EACH ROW EXECUTE FUNCTION public.guard_match_spectator_bet_insert();

-- Direct updates may cancel a creator's pending event offer only. Acceptance must
-- use accept_spectator_bet(), otherwise no stake would be escrowed.
DROP POLICY IF EXISTS "Users can update spectator bets" ON public.event_spectator_bets;
DROP POLICY IF EXISTS "Users can update their spectator bets" ON public.event_spectator_bets;
DROP POLICY IF EXISTS "Creators can cancel pending event spectator bets" ON public.event_spectator_bets;
CREATE POLICY "Creators can cancel pending event spectator bets"
ON public.event_spectator_bets FOR UPDATE TO authenticated
USING (auth.uid() = creator_id AND status = 'pending')
WITH CHECK (auth.uid() = creator_id AND status = 'cancelled'
            AND acceptor_id IS NULL AND winner_id IS NULL
            AND COALESCE(stakes_locked,false) = false);

REVOKE INSERT, UPDATE, DELETE ON public.event_bets, public.spectator_bets,
  public.event_spectator_bets FROM anon;
REVOKE UPDATE, DELETE ON public.event_bets FROM authenticated;
REVOKE DELETE ON public.spectator_bets, public.event_spectator_bets FROM authenticated;
GRANT SELECT, INSERT ON public.event_bets TO authenticated;
GRANT SELECT, INSERT, UPDATE ON public.spectator_bets, public.event_spectator_bets TO authenticated;

-- Apply the same 10% commission as normal matches to escrowed spectator bets.
-- Old accepted bets without locked stakes are voided: settlement must never debit
-- a player after the fact.
CREATE OR REPLACE FUNCTION public.resolve_spectator_bets()
RETURNS trigger
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_bet public.spectator_bets%ROWTYPE;
  v_winner uuid;
  v_loser uuid;
  v_before numeric;
  v_pot numeric;
  v_fee numeric;
  v_payout numeric;
  v_is_sandbox boolean := COALESCE(NEW.is_sandbox,true);
  v_has_winner boolean := NEW.status='completed' AND NEW.winner_id IS NOT NULL;
BEGIN
  IF NOT (NEW.status IN ('completed','abandoned')
          AND (TG_OP='INSERT' OR OLD.status IS NULL OR OLD.status NOT IN ('completed','abandoned'))) THEN
    RETURN NEW;
  END IF;

  FOR v_bet IN SELECT * FROM public.spectator_bets
    WHERE game_id=NEW.id AND status='accepted' AND acceptor_id IS NOT NULL
    ORDER BY id FOR UPDATE
  LOOP
    IF NOT COALESCE(v_bet.stakes_locked,false) THEN
      UPDATE public.spectator_bets SET status='cancelled',resolved_at=now() WHERE id=v_bet.id;
      CONTINUE;
    END IF;

    IF v_has_winner THEN
      IF v_bet.creator_bet_on=NEW.winner_id THEN
        v_winner:=v_bet.creator_id; v_loser:=v_bet.acceptor_id;
      ELSE
        v_winner:=v_bet.acceptor_id; v_loser:=v_bet.creator_id;
      END IF;
      v_pot:=v_bet.amount*2;
      v_fee:=round(v_pot*0.10,2);
      v_payout:=v_pot-v_fee;
      IF v_is_sandbox THEN
        SELECT sandbox_balance INTO v_before FROM public.wallets WHERE user_id=v_winner FOR UPDATE;
        UPDATE public.wallets SET sandbox_balance=sandbox_balance+v_payout,updated_at=now() WHERE user_id=v_winner;
      ELSE
        SELECT balance INTO v_before FROM public.wallets WHERE user_id=v_winner FOR UPDATE;
        UPDATE public.wallets SET balance=balance+v_payout,updated_at=now() WHERE user_id=v_winner;
      END IF;
      IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
      v_before:=COALESCE(v_before,0);
      INSERT INTO public.transactions
        (user_id,type,amount,balance_before,balance_after,is_sandbox,game_id,description,metadata)
      VALUES
        (v_winner,'spectator_bet_win',v_payout,v_before,v_before+v_payout,v_is_sandbox,NEW.id,
         'Pari spectateur gagne',jsonb_build_object('bet_id',v_bet.id,'opponent_id',v_loser,
         'bet_type','spectator','escrow',true,'platform_fee',v_fee));
      UPDATE public.spectator_bets SET status='completed',winner_id=v_winner,resolved_at=now() WHERE id=v_bet.id;
    ELSE
      IF v_is_sandbox THEN
        SELECT sandbox_balance INTO v_before FROM public.wallets WHERE user_id=v_bet.creator_id FOR UPDATE;
        UPDATE public.wallets SET sandbox_balance=sandbox_balance+v_bet.amount,updated_at=now() WHERE user_id=v_bet.creator_id;
      ELSE
        SELECT balance INTO v_before FROM public.wallets WHERE user_id=v_bet.creator_id FOR UPDATE;
        UPDATE public.wallets SET balance=balance+v_bet.amount,updated_at=now() WHERE user_id=v_bet.creator_id;
      END IF;
      IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
      INSERT INTO public.transactions (user_id,type,amount,balance_before,balance_after,is_sandbox,game_id,description,metadata)
      VALUES (v_bet.creator_id,'refund',v_bet.amount,COALESCE(v_before,0),COALESCE(v_before,0)+v_bet.amount,
        v_is_sandbox,NEW.id,'Remboursement pari spectateur',jsonb_build_object('bet_id',v_bet.id,'bet_type','spectator'));

      IF v_is_sandbox THEN
        SELECT sandbox_balance INTO v_before FROM public.wallets WHERE user_id=v_bet.acceptor_id FOR UPDATE;
        UPDATE public.wallets SET sandbox_balance=sandbox_balance+v_bet.amount,updated_at=now() WHERE user_id=v_bet.acceptor_id;
      ELSE
        SELECT balance INTO v_before FROM public.wallets WHERE user_id=v_bet.acceptor_id FOR UPDATE;
        UPDATE public.wallets SET balance=balance+v_bet.amount,updated_at=now() WHERE user_id=v_bet.acceptor_id;
      END IF;
      IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
      INSERT INTO public.transactions (user_id,type,amount,balance_before,balance_after,is_sandbox,game_id,description,metadata)
      VALUES (v_bet.acceptor_id,'refund',v_bet.amount,COALESCE(v_before,0),COALESCE(v_before,0)+v_bet.amount,
        v_is_sandbox,NEW.id,'Remboursement pari spectateur',jsonb_build_object('bet_id',v_bet.id,'bet_type','spectator'));
      UPDATE public.spectator_bets SET status='cancelled',resolved_at=now() WHERE id=v_bet.id;
    END IF;
  END LOOP;

  UPDATE public.spectator_bets SET status='expired'
  WHERE game_id=NEW.id AND status='pending';
  RETURN NEW;
END;
$$;

-- Event settlement uses the wallet mode captured when the stake was locked.
-- A side with no winning ticket receives a full refund, and accepted
-- spectator escrows use the same 10% commission as every other paid match.
CREATE OR REPLACE FUNCTION public.settle_admin_event(p_event_id uuid, p_winner text)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $$
DECLARE
  v_event public.events%ROWTYPE;
  v_bet public.event_bets%ROWTYPE;
  v_spectator public.event_spectator_bets%ROWTYPE;
  v_wallet public.wallets%ROWTYPE;
  v_before numeric;
  v_after numeric;
  v_total_pool numeric := 0;
  v_winning_pool numeric := 0;
  v_payout numeric;
  v_fee numeric;
  v_winner_id uuid;
  v_loser_id uuid;
  v_pool_count integer := 0;
  v_spectator_count integer := 0;
  v_voided_count integer := 0;
BEGIN
  IF NOT public.is_tournament_operator() THEN
    RAISE EXCEPTION 'forbidden' USING ERRCODE='42501';
  END IF;
  IF p_winner NOT IN ('a','b') THEN RAISE EXCEPTION 'invalid_winner'; END IF;

  SELECT * INTO v_event FROM public.events WHERE id=p_event_id FOR UPDATE;
  IF NOT FOUND THEN RAISE EXCEPTION 'event_not_found'; END IF;
  IF v_event.status IN ('completed','cancelled') THEN RAISE EXCEPTION 'event_already_resolved'; END IF;

  SELECT COALESCE(sum(amount),0),
         COALESCE(sum(amount) FILTER (WHERE bet_on=p_winner),0),
         count(*)
  INTO v_total_pool,v_winning_pool,v_pool_count
  FROM public.event_bets WHERE event_id=p_event_id AND status='pending';

  FOR v_bet IN SELECT * FROM public.event_bets
    WHERE event_id=p_event_id AND status='pending'
    ORDER BY user_id,id FOR UPDATE
  LOOP
    IF v_winning_pool>0 AND v_bet.bet_on=p_winner THEN
      v_payout:=floor((v_bet.amount/v_winning_pool)*(v_total_pool*0.90));
      v_fee:=round((v_bet.amount/v_winning_pool)*(v_total_pool*0.10),2);
      SELECT * INTO v_wallet FROM public.wallets WHERE user_id=v_bet.user_id FOR UPDATE;
      IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
      v_before:=CASE WHEN v_bet.is_sandbox THEN COALESCE(v_wallet.sandbox_balance,0)
                     ELSE COALESCE(v_wallet.balance,0) END;
      v_after:=v_before+v_payout;
      IF v_bet.is_sandbox THEN
        UPDATE public.wallets SET sandbox_balance=v_after,updated_at=now() WHERE id=v_wallet.id;
      ELSE
        UPDATE public.wallets SET balance=v_after,updated_at=now() WHERE id=v_wallet.id;
      END IF;
      INSERT INTO public.transactions
        (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
      VALUES
        (v_bet.user_id,'bet_won',v_payout,v_before,v_after,v_bet.is_sandbox,'Gain pari evenement',
         jsonb_build_object('event_id',p_event_id,'event_bet_id',v_bet.id,'settled_by',auth.uid(),
         'escrow',true,'platform_fee',v_fee));
      UPDATE public.event_bets SET status='won' WHERE id=v_bet.id;
    ELSIF v_winning_pool=0 THEN
      v_payout:=v_bet.amount;
      SELECT * INTO v_wallet FROM public.wallets WHERE user_id=v_bet.user_id FOR UPDATE;
      IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
      v_before:=CASE WHEN v_bet.is_sandbox THEN COALESCE(v_wallet.sandbox_balance,0)
                     ELSE COALESCE(v_wallet.balance,0) END;
      v_after:=v_before+v_payout;
      IF v_bet.is_sandbox THEN
        UPDATE public.wallets SET sandbox_balance=v_after,updated_at=now() WHERE id=v_wallet.id;
      ELSE
        UPDATE public.wallets SET balance=v_after,updated_at=now() WHERE id=v_wallet.id;
      END IF;
      INSERT INTO public.transactions
        (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
      VALUES
        (v_bet.user_id,'refund',v_payout,v_before,v_after,v_bet.is_sandbox,
         'Remboursement integral pari evenement sans gagnant',
         jsonb_build_object('event_id',p_event_id,'event_bet_id',v_bet.id,'settled_by',auth.uid(),
         'escrow',true,'platform_fee',0));
      UPDATE public.event_bets SET status='refunded' WHERE id=v_bet.id;
    ELSE
      UPDATE public.event_bets SET status='lost' WHERE id=v_bet.id;
    END IF;
  END LOOP;

  FOR v_spectator IN SELECT * FROM public.event_spectator_bets
    WHERE event_id=p_event_id AND status='accepted'
    ORDER BY id FOR UPDATE
  LOOP
    IF NOT COALESCE(v_spectator.stakes_locked,false) THEN
      UPDATE public.event_spectator_bets
      SET status='cancelled',resolved_at=now() WHERE id=v_spectator.id;
      v_voided_count:=v_voided_count+1;
      CONTINUE;
    END IF;
    IF v_spectator.creator_bet_on=p_winner THEN
      v_winner_id:=v_spectator.creator_id; v_loser_id:=v_spectator.acceptor_id;
    ELSE
      v_winner_id:=v_spectator.acceptor_id; v_loser_id:=v_spectator.creator_id;
    END IF;
    IF v_winner_id IS NULL OR v_loser_id IS NULL THEN RAISE EXCEPTION 'invalid_spectator_bet'; END IF;

    v_fee:=round((v_spectator.amount*2)*0.10,2);
    v_payout:=(v_spectator.amount*2)-v_fee;
    SELECT * INTO v_wallet FROM public.wallets WHERE user_id=v_winner_id FOR UPDATE;
    IF NOT FOUND THEN RAISE EXCEPTION 'wallet_not_found'; END IF;
    v_before:=CASE WHEN v_spectator.is_sandbox THEN COALESCE(v_wallet.sandbox_balance,0)
                   ELSE COALESCE(v_wallet.balance,0) END;
    v_after:=v_before+v_payout;
    IF v_spectator.is_sandbox THEN
      UPDATE public.wallets SET sandbox_balance=v_after,updated_at=now() WHERE id=v_wallet.id;
    ELSE
      UPDATE public.wallets SET balance=v_after,updated_at=now() WHERE id=v_wallet.id;
    END IF;
    INSERT INTO public.transactions
      (user_id,type,amount,balance_before,balance_after,is_sandbox,description,metadata)
    VALUES
      (v_winner_id,'spectator_bet_win',v_payout,v_before,v_after,v_spectator.is_sandbox,
       'Gain pari evenement entre spectateurs',
       jsonb_build_object('event_id',p_event_id,'spectator_bet_id',v_spectator.id,'escrow',true,
       'opponent_id',v_loser_id,'platform_fee',v_fee));
    UPDATE public.event_spectator_bets
    SET status='completed',winner_id=v_winner_id,resolved_at=now() WHERE id=v_spectator.id;
    v_spectator_count:=v_spectator_count+1;
  END LOOP;

  UPDATE public.event_spectator_bets SET status='expired',resolved_at=now()
  WHERE event_id=p_event_id AND status='pending';
  UPDATE public.events
  SET status='completed',winner=p_winner,ended_at=now(),updated_at=now()
  WHERE id=p_event_id;

  RETURN jsonb_build_object('success',true,'pool_bets',v_pool_count,
    'spectator_bets',v_spectator_count,'voided_spectator_bets',v_voided_count);
END;
$$;

-- Tournament prize settlement for the current test phase. The existing real
-- bracket and its scheduling function are intentionally unchanged.
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

DROP TRIGGER IF EXISTS pay_sandbox_tournament_prizes ON public.tournaments;
CREATE TRIGGER pay_sandbox_tournament_prizes
AFTER UPDATE OF status ON public.tournaments
FOR EACH ROW EXECUTE FUNCTION public.pay_sandbox_tournament_prizes();

-- Never mark a server result as synchronized when wallet settlement failed.
DO $$
DECLARE
  v_definition text;
  v_old text := E'EXCEPTION\n  WHEN OTHERS THEN\n    RAISE WARNING ''settle_game_wallets error for game %: %'', p_game_id, SQLERRM;\nEND;';
  v_new text := E'EXCEPTION\n  WHEN OTHERS THEN\n    RAISE;\nEND;';
BEGIN
  SELECT pg_get_functiondef('public.settle_game_wallets(uuid)'::regprocedure) INTO v_definition;
  IF position(v_old IN v_definition)=0 THEN
    RAISE EXCEPTION 'Unexpected settle_game_wallets definition; refusing an unsafe partial patch';
  END IF;
  EXECUTE replace(v_definition,v_old,v_new);
END;
$$;

REVOKE ALL ON FUNCTION public.guard_event_bet_insert() FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.guard_match_spectator_bet_insert() FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.resolve_spectator_bets() FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.pay_sandbox_tournament_prizes() FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.place_event_bet(uuid,text,numeric) TO authenticated;
REVOKE ALL ON FUNCTION public.settle_admin_event(uuid,text) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.settle_admin_event(uuid,text) TO authenticated, service_role;

COMMIT;
