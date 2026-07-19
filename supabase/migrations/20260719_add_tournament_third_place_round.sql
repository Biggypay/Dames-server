-- The bronze match determines ranks only. Rewards remain limited to first and
-- second place, as configured by the tournament administrator.
ALTER TYPE public.tournament_round ADD VALUE IF NOT EXISTS 'third_place' AFTER 'semi';

ALTER TABLE public.tournaments
  ADD COLUMN IF NOT EXISTS ceremony_at timestamptz;

COMMENT ON COLUMN public.tournaments.ceremony_at IS
  'Scheduled closing ceremony time; tournament matches remain authoritative independently.';
