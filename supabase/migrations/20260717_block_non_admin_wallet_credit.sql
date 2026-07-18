-- Ferme la faille où un participant d'une partie terminée pouvait se
-- créditer lui-même jusqu'à 2x la mise via credit_user. Les crédits (gains)
-- sont réglés exclusivement par le serveur (submit_game_result, exécuté en
-- service_role) ou par un admin. Aucun joueur non-admin ne peut créditer.
CREATE OR REPLACE FUNCTION public._wallet_op_authorized(p_caller uuid, p_target uuid, p_amount numeric, p_game_id uuid, p_operation text)
 RETURNS boolean
 LANGUAGE plpgsql
 STABLE SECURITY DEFINER
 SET search_path TO 'public'
AS $function$
DECLARE
  v_game RECORD;
BEGIN
  IF p_caller IS NULL THEN RETURN false; END IF;
  IF p_amount IS NULL OR p_amount <= 0 THEN RETURN false; END IF;

  -- Admin can perform any wallet operation
  IF public.has_role(p_caller, 'admin') THEN RETURN true; END IF;

  -- Non-admin callers may NEVER credit a wallet. Winner payouts are settled
  -- server-side only (submit_game_result, run as service_role). This removes
  -- the path where a completed-game participant could self-credit.
  IF p_operation = 'credit' THEN
    RETURN false;
  END IF;

  -- Non-admin operations MUST reference a game context
  IF p_game_id IS NULL THEN RETURN false; END IF;

  SELECT * INTO v_game FROM public.games WHERE id = p_game_id;
  IF v_game IS NULL THEN RETURN false; END IF;

  -- Caller and target must both be participants of the game
  IF p_caller <> v_game.player1_id AND p_caller <> v_game.player2_id THEN RETURN false; END IF;
  IF p_target <> v_game.player1_id AND p_target <> v_game.player2_id THEN RETURN false; END IF;

  -- The game must be finished for settlement/refund operations
  IF v_game.status <> 'completed' THEN RETURN false; END IF;

  -- Amount ceilings anchored to the game's bet_amount
  IF p_operation = 'debit' THEN
    IF p_amount > COALESCE(v_game.bet_amount, 0) THEN RETURN false; END IF;
  ELSE
    RETURN false;
  END IF;

  RETURN true;
END;
$function$;
