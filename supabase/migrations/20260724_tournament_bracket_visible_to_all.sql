-- The bracket (tournament_matches) was only visible to admins and the
-- tournament's own participants, so ordinary players — and anyone removed from
-- the tournament — saw the flat participant list instead of the bracket. Make
-- matches of any non-draft tournament readable by every authenticated user,
-- mirroring how participants of non-draft tournaments are already visible.
DROP POLICY IF EXISTS "Participants and admins view tournament matches" ON public.tournament_matches;
CREATE POLICY "Anyone can view matches of visible tournaments"
ON public.tournament_matches FOR SELECT TO authenticated
USING (
  EXISTS (
    SELECT 1 FROM public.tournaments t
    WHERE t.id = tournament_matches.tournament_id
      AND (t.status <> 'draft'::public.tournament_status OR public.has_role(auth.uid(), 'admin'::public.app_role))
  )
);
