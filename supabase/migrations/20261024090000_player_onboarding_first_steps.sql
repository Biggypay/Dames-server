-- Premiers pas : 76 % des inscrits n'avaient jamais joué une partie. Un
-- joueur qui n'a encore rien joué est accueilli par une première partie de
-- Dames contre l'IA. Cette table retient seulement qu'il a fini ou passé cet
-- accueil ; elle ne touche ni au portefeuille ni aux profils publics.
CREATE TABLE IF NOT EXISTS public.player_onboarding (
  user_id uuid PRIMARY KEY REFERENCES auth.users(id) ON DELETE CASCADE,
  completed_at timestamptz NOT NULL DEFAULT now(),
  outcome text NOT NULL CHECK (outcome IN ('win', 'loss', 'draw', 'skipped'))
);

ALTER TABLE public.player_onboarding ENABLE ROW LEVEL SECURITY;

DROP POLICY IF EXISTS "Players read their own onboarding" ON public.player_onboarding;
CREATE POLICY "Players read their own onboarding"
  ON public.player_onboarding FOR SELECT TO authenticated
  USING (user_id = auth.uid());

-- Aucune écriture directe : seul complete_onboarding() écrit, pour soi.
REVOKE ALL ON public.player_onboarding FROM anon, authenticated;
GRANT SELECT ON public.player_onboarding TO authenticated;

-- L'accueil s'affiche à un compte actif qui n'a jamais joué en ligne et ne
-- l'a ni terminé ni passé.
CREATE OR REPLACE FUNCTION public.get_my_onboarding_state()
RETURNS jsonb
LANGUAGE plpgsql
STABLE
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_uid uuid := auth.uid();
  v_done boolean;
  v_played boolean;
  v_active boolean;
BEGIN
  IF v_uid IS NULL THEN
    RETURN jsonb_build_object('needs_onboarding', false);
  END IF;
  SELECT EXISTS (SELECT 1 FROM public.player_onboarding WHERE user_id = v_uid) INTO v_done;
  SELECT EXISTS (SELECT 1 FROM public.games WHERE player1_id = v_uid OR player2_id = v_uid) INTO v_played;
  SELECT COALESCE((SELECT account_status = 'active' FROM public.profiles WHERE id = v_uid), false) INTO v_active;
  RETURN jsonb_build_object(
    'needs_onboarding', v_active AND NOT v_done AND NOT v_played,
    'completed', v_done,
    'has_played', v_played
  );
END;
$$;

CREATE OR REPLACE FUNCTION public.complete_onboarding(p_outcome text)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_uid uuid := auth.uid();
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;
  IF p_outcome IS NULL OR p_outcome NOT IN ('win', 'loss', 'draw', 'skipped') THEN
    RAISE EXCEPTION 'invalid onboarding outcome' USING ERRCODE = '22023';
  END IF;
  -- Le premier aboutissement fait foi ; un second appel ne change rien.
  INSERT INTO public.player_onboarding (user_id, outcome)
  VALUES (v_uid, p_outcome)
  ON CONFLICT (user_id) DO NOTHING;
END;
$$;

REVOKE ALL ON FUNCTION public.get_my_onboarding_state() FROM PUBLIC, anon;
REVOKE ALL ON FUNCTION public.complete_onboarding(text) FROM PUBLIC, anon;
GRANT EXECUTE ON FUNCTION public.get_my_onboarding_state() TO authenticated;
GRANT EXECUTE ON FUNCTION public.complete_onboarding(text) TO authenticated;
