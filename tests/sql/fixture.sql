-- Schema minimal mais fidele (colonnes reelles tirees de la production) pour
-- valider les deux migrations hors production.
CREATE SCHEMA IF NOT EXISTS auth;
CREATE SCHEMA IF NOT EXISTS private;

CREATE TYPE public.game_type AS ENUM ('checkers','chess','tictactoe','quoridor','penalty_shootout','rock_paper_scissors','ludo','dominos');
CREATE TYPE public.game_status AS ENUM ('waiting','in_progress','completed','abandoned');
CREATE TYPE public.game_result AS ENUM ('win','loss','draw','mutual_quit','timeout','abandoned');
CREATE TYPE public.tournament_round AS ENUM ('group','round_of_16','quarter','semi','third_place','final');
CREATE TYPE public.tournament_status AS ENUM ('draft','registration_open','registration_closed','drawing','awaiting_start','in_progress','completed','cancelled');
CREATE TYPE public.tournament_match_status AS ENUM ('pending','ready','in_progress','completed','walkover','cancelled');
CREATE TYPE public.tournament_participant_status AS ENUM ('active','eliminated','winner');
CREATE TYPE public.app_role AS ENUM ('user','admin','super_admin');

CREATE TABLE auth.users (id uuid PRIMARY KEY, email text);

CREATE FUNCTION auth.uid() RETURNS uuid LANGUAGE sql STABLE AS
  $$ SELECT nullif(current_setting('test.uid', true), '')::uuid $$;
CREATE FUNCTION auth.role() RETURNS text LANGUAGE sql STABLE AS
  $$ SELECT coalesce(nullif(current_setting('test.role', true), ''), 'authenticated') $$;

CREATE TABLE public.games (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  game_type public.game_type NOT NULL,
  player1_id uuid,
  player2_id uuid,
  is_ai_opponent boolean NOT NULL DEFAULT false,
  bet_amount numeric NOT NULL,
  is_sandbox boolean NOT NULL DEFAULT true,
  status public.game_status NOT NULL DEFAULT 'waiting',
  winner_id uuid,
  result public.game_result,
  platform_fee numeric NOT NULL DEFAULT 0,
  started_at timestamptz,
  completed_at timestamptz,
  duration_seconds integer,
  created_at timestamptz NOT NULL DEFAULT now(),
  updated_at timestamptz NOT NULL DEFAULT now(),
  last_move_at timestamptz,
  current_turn_player_id uuid,
  turn_started_at timestamptz,
  game_settings jsonb DEFAULT '{}'::jsonb,
  player1_bet_amount numeric DEFAULT 50,
  player2_bet_amount numeric DEFAULT 50,
  player1_is_ready boolean DEFAULT false,
  player2_is_ready boolean DEFAULT false,
  pregame_started_at timestamptz,
  player1_last_heartbeat timestamptz,
  player2_last_heartbeat timestamptz,
  tournament_match_id uuid,
  is_tournament boolean NOT NULL DEFAULT false,
  server_live_at timestamptz
);

CREATE TABLE public.tournaments (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  name text NOT NULL,
  game_type text NOT NULL,
  starts_at timestamptz,
  max_participants integer NOT NULL DEFAULT 32,
  entry_fee numeric NOT NULL DEFAULT 1000,
  rewards jsonb NOT NULL DEFAULT '{"first": 0, "second": 0}'::jsonb,
  status public.tournament_status NOT NULL DEFAULT 'draft',
  registration_enabled boolean NOT NULL DEFAULT true,
  winner_id uuid,
  created_at timestamptz NOT NULL DEFAULT now(),
  updated_at timestamptz NOT NULL DEFAULT now(),
  auto_launch boolean NOT NULL DEFAULT true,
  tournament_timezone text NOT NULL DEFAULT 'America/Port-au-Prince'
);

CREATE TABLE public.tournament_matches (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  tournament_id uuid NOT NULL,
  round public.tournament_round NOT NULL,
  group_letter char(1),
  bracket_position integer NOT NULL,
  next_match_id uuid,
  player1_id uuid,
  player2_id uuid,
  winner_id uuid,
  loser_id uuid,
  score text,
  game_id uuid,
  scheduled_at timestamptz,
  ready_at timestamptz,
  played_at timestamptz,
  status public.tournament_match_status NOT NULL DEFAULT 'pending',
  created_at timestamptz NOT NULL DEFAULT now(),
  updated_at timestamptz NOT NULL DEFAULT now(),
  player1_joined_at timestamptz,
  player2_joined_at timestamptz,
  forfeit_processed boolean NOT NULL DEFAULT false,
  lockout_notified_1h boolean NOT NULL DEFAULT false,
  player1_reported_winner uuid,
  player2_reported_winner uuid,
  result_conflict boolean NOT NULL DEFAULT false,
  reminder_notified_5min boolean NOT NULL DEFAULT false,
  start_notified_at timestamptz,
  final_reminder_notified_at timestamptz,
  player1_slot_vacant boolean NOT NULL DEFAULT false,
  player2_slot_vacant boolean NOT NULL DEFAULT false,
  vacancy_propagated_at timestamptz,
  wildcard_user_id uuid,
  player1_last_seen_at timestamptz,
  player2_last_seen_at timestamptz
);

CREATE TABLE public.tournament_participants (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  tournament_id uuid NOT NULL,
  user_id uuid NOT NULL,
  group_letter char(1),
  seed integer,
  status public.tournament_participant_status NOT NULL DEFAULT 'active',
  eliminated_at_round public.tournament_round,
  final_rank integer,
  created_at timestamptz NOT NULL DEFAULT now(),
  updated_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE public.notifications (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id uuid NOT NULL,
  type text NOT NULL,
  title text NOT NULL,
  message text NOT NULL,
  data jsonb,
  read boolean NOT NULL DEFAULT false,
  created_at timestamptz NOT NULL DEFAULT now(),
  expires_at timestamptz,
  status text DEFAULT 'pending'
);

CREATE TABLE public.admin_logs (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  admin_id uuid NOT NULL,
  admin_email text NOT NULL,
  action text NOT NULL,
  target_user_id uuid,
  target_user_email text,
  details jsonb,
  status text NOT NULL DEFAULT 'success',
  created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE public.user_roles (
  id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
  user_id uuid NOT NULL,
  role public.app_role NOT NULL DEFAULT 'user',
  created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE private.game_server_room_states (
  game_type text NOT NULL,
  room_id text NOT NULL,
  game_id uuid,
  status text NOT NULL,
  state jsonb NOT NULL,
  updated_at timestamptz NOT NULL DEFAULT now(),
  PRIMARY KEY (game_type, room_id)
);

CREATE FUNCTION public.has_role(_user_id uuid, _role public.app_role)
RETURNS boolean LANGUAGE sql STABLE AS
  $$ SELECT EXISTS (SELECT 1 FROM public.user_roles WHERE user_id = _user_id AND role = _role) $$;

CREATE FUNCTION public.is_tournament_operator() RETURNS boolean LANGUAGE sql STABLE AS
  $$ SELECT public.has_role(auth.uid(), 'admin'::public.app_role)
         OR public.has_role(auth.uid(), 'super_admin'::public.app_role)
         OR auth.role() = 'service_role' $$;

CREATE FUNCTION public.game_heartbeat_stale_seconds() RETURNS integer LANGUAGE sql STABLE AS $$ SELECT 40 $$;
CREATE FUNCTION public.tournament_presence_window_seconds() RETURNS integer LANGUAGE sql STABLE AS $$ SELECT 120 $$;

-- Stub : la vraie fonction reglera la partie ; ici elle ne conclut rien, ce qui
-- laisse `get_game_resume_offer` aller jusqu'au bout de sa logique.
CREATE FUNCTION public.finalize_abandoned_game(p_game_id uuid, p_dry_run boolean DEFAULT false)
RETURNS text LANGUAGE sql AS $$ SELECT 'not_eligible'::text $$;
