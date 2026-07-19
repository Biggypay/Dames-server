-- Tournament scheduling is authoritative in Haiti time.  Reaching 32 players
-- never starts a tournament in the evening: the first match is at the next
-- eligible 09:00 America/Port-au-Prince slot.

CREATE OR REPLACE FUNCTION public.next_tournament_start(p_reference timestamptz)
RETURNS timestamptz
LANGUAGE sql
STABLE
SET search_path = public, pg_temp
AS $$
  WITH local_reference AS (
    SELECT COALESCE(p_reference, now()) AT TIME ZONE 'America/Port-au-Prince' AS value
  )
  SELECT (
    value::date
    + CASE WHEN value::time <= time '09:00' THEN 0 ELSE 1 END
    + time '09:00'
  ) AT TIME ZONE 'America/Port-au-Prince'
  FROM local_reference;
$$;

REVOKE ALL ON FUNCTION public.next_tournament_start(timestamptz) FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.next_tournament_start(timestamptz) TO service_role;

CREATE OR REPLACE FUNCTION public.start_tournament_draw(p_tournament_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_ends timestamptz := now() + interval '10 minutes';
  v_starts timestamptz := public.next_tournament_start(v_ends);
BEGIN
  IF NOT public.is_tournament_operator() AND pg_trigger_depth() = 0 THEN
    RAISE EXCEPTION 'forbidden';
  END IF;

  UPDATE public.tournaments
     SET status = 'drawing',
         draw_started_at = now(),
         draw_ends_at = v_ends,
         draw_notified_5min = false,
         starts_at = v_starts,
         registration_enabled = false,
         updated_at = now()
   WHERE id = p_tournament_id
     AND status IN ('registration_open', 'registration_closed');

  IF NOT FOUND THEN
    RETURN;
  END IF;

  INSERT INTO public.notifications (user_id, type, title, message, data, status)
  SELECT tp.user_id,
         'admin_announcement',
         '🎲 Tirage au sort en cours',
         'Le tournoi est complet. Les groupes et les horaires seront publiés après le tirage. Le premier match est prévu le '
           || to_char(v_starts AT TIME ZONE 'America/Port-au-Prince', 'DD/MM/YYYY à HH24:MI') || '.',
         jsonb_build_object(
           'tournament_id', p_tournament_id,
           'kind', 'tournament_draw_started',
           'draw_ends_at', v_ends,
           'starts_at', v_starts,
           'timezone', 'America/Port-au-Prince'
         ),
         'unread'
    FROM public.tournament_participants tp
   WHERE tp.tournament_id = p_tournament_id;
END;
$$;

CREATE OR REPLACE FUNCTION public.schedule_tournament_matches(p_tournament_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_reference timestamptz;
  v_start timestamptz;
  v_day1 date;
  v_timezone constant text := 'America/Port-au-Prince';
  v_match record;
  v_day integer;
  v_hour integer;
  v_minute integer;
BEGIN
  IF NOT public.is_tournament_operator() AND pg_trigger_depth() = 0 THEN
    RAISE EXCEPTION 'forbidden';
  END IF;

  SELECT COALESCE(draw_ends_at, starts_at, now())
    INTO v_reference
    FROM public.tournaments
   WHERE id = p_tournament_id
   FOR UPDATE;

  IF NOT FOUND THEN
    RAISE EXCEPTION 'tournament_not_found';
  END IF;

  v_start := public.next_tournament_start(v_reference);
  v_day1 := (v_start AT TIME ZONE v_timezone)::date;

  FOR v_match IN
    SELECT id, round, group_letter, bracket_position
      FROM public.tournament_matches
     WHERE tournament_id = p_tournament_id
  LOOP
    v_day := NULL;
    v_hour := NULL;
    v_minute := 0;

    IF v_match.round = 'group' THEN
      IF v_match.group_letter = 'A' THEN
        v_day := 1; v_hour := 8 + v_match.bracket_position;
      ELSIF v_match.group_letter = 'B' THEN
        v_day := 1; v_hour := 13 + v_match.bracket_position;
      ELSIF v_match.group_letter = 'C' THEN
        v_day := 2; v_hour := 8 + v_match.bracket_position;
      ELSIF v_match.group_letter = 'D' THEN
        v_day := 2; v_hour := 13 + v_match.bracket_position;
      END IF;
    ELSIF v_match.round = 'round_of_16' THEN
      v_day := 3;
      IF v_match.bracket_position <= 4 THEN
        v_hour := 8 + v_match.bracket_position;
      ELSE
        v_hour := 13 + (v_match.bracket_position - 4);
      END IF;
    ELSIF v_match.round = 'quarter' THEN
      v_day := 4;
      v_hour := CASE v_match.bracket_position
        WHEN 1 THEN 9 WHEN 2 THEN 10 WHEN 3 THEN 14 WHEN 4 THEN 15
      END;
    ELSIF v_match.round = 'semi' THEN
      v_day := 5;
      v_hour := CASE v_match.bracket_position WHEN 1 THEN 9 ELSE 14 END;
    ELSIF v_match.round = 'third_place' THEN
      v_day := 6; v_hour := 14;
    ELSIF v_match.round = 'final' THEN
      v_day := 6; v_hour := 15; v_minute := 30;
    END IF;

    IF v_day IS NOT NULL AND v_hour IS NOT NULL THEN
      UPDATE public.tournament_matches
         SET scheduled_at = (
           (v_day1 + (v_day - 1)) + make_time(v_hour, v_minute, 0)
         ) AT TIME ZONE v_timezone,
             updated_at = now()
       WHERE id = v_match.id;
    END IF;
  END LOOP;

  UPDATE public.tournaments
     SET starts_at = v_start,
         ceremony_at = ((v_day1 + 5) + time '17:00') AT TIME ZONE v_timezone,
         matches_scheduled = true,
         updated_at = now()
   WHERE id = p_tournament_id;
END;
$$;

CREATE OR REPLACE FUNCTION public.launch_tournament(p_tournament_id uuid, p_auto boolean DEFAULT true)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_shuffled uuid[];
  v_count integer;
  v_i integer;
  v_group char(1);
  v_group_index integer;
  v_in_group integer;
  v_match_id uuid;
  v_round_of_16_ids uuid[];
  v_quarter_ids uuid[];
  v_semi_ids uuid[];
  v_final_id uuid;
  v_third_place_id uuid;
  v_current_status public.tournament_status;
  v_start timestamptz;
BEGIN
  IF NOT public.is_tournament_operator() THEN
    RAISE EXCEPTION 'forbidden';
  END IF;

  SELECT status INTO v_current_status
    FROM public.tournaments
   WHERE id = p_tournament_id
   FOR UPDATE;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'tournament_not_found';
  END IF;

  IF EXISTS (
    SELECT 1 FROM public.tournament_matches WHERE tournament_id = p_tournament_id
  ) THEN
    PERFORM public.schedule_tournament_matches(p_tournament_id);
    IF v_current_status IN ('registration_open', 'registration_closed', 'drawing', 'awaiting_start') THEN
      UPDATE public.tournaments
         SET status = 'awaiting_start', registration_enabled = false, updated_at = now()
       WHERE id = p_tournament_id;
    END IF;
    SELECT starts_at INTO v_start FROM public.tournaments WHERE id = p_tournament_id;
    RETURN jsonb_build_object(
      'success', true,
      'already_built', true,
      'status', CASE WHEN v_current_status = 'in_progress' THEN 'in_progress' ELSE 'awaiting_start' END,
      'starts_at', v_start
    );
  END IF;

  SELECT array_agg(user_id ORDER BY random())
    INTO v_shuffled
    FROM public.tournament_participants
   WHERE tournament_id = p_tournament_id
     AND status = 'active';

  v_count := COALESCE(array_length(v_shuffled, 1), 0);
  IF v_count <> 32 THEN
    RAISE EXCEPTION 'Le tournoi doit avoir exactement 32 participants (actuellement %)', v_count;
  END IF;

  FOR v_i IN 1..32 LOOP
    v_group_index := ((v_i - 1) / 8);
    v_group := CASE v_group_index WHEN 0 THEN 'A' WHEN 1 THEN 'B' WHEN 2 THEN 'C' ELSE 'D' END;
    UPDATE public.tournament_participants
       SET group_letter = v_group, seed = v_i, status = 'active',
           eliminated_at_round = NULL, final_rank = NULL, updated_at = now()
     WHERE tournament_id = p_tournament_id
       AND user_id = v_shuffled[v_i];
  END LOOP;

  INSERT INTO public.tournament_matches (tournament_id, round, bracket_position)
  VALUES (p_tournament_id, 'final', 1)
  RETURNING id INTO v_final_id;

  INSERT INTO public.tournament_matches (tournament_id, round, bracket_position)
  VALUES (p_tournament_id, 'third_place', 1)
  RETURNING id INTO v_third_place_id;

  v_semi_ids := ARRAY[]::uuid[];
  FOR v_i IN 1..2 LOOP
    INSERT INTO public.tournament_matches (tournament_id, round, bracket_position, next_match_id)
    VALUES (p_tournament_id, 'semi', v_i, v_final_id)
    RETURNING id INTO v_match_id;
    v_semi_ids := v_semi_ids || v_match_id;
  END LOOP;

  v_quarter_ids := ARRAY[]::uuid[];
  FOR v_i IN 1..4 LOOP
    INSERT INTO public.tournament_matches (tournament_id, round, bracket_position, next_match_id)
    VALUES (p_tournament_id, 'quarter', v_i, v_semi_ids[((v_i - 1) / 2) + 1])
    RETURNING id INTO v_match_id;
    v_quarter_ids := v_quarter_ids || v_match_id;
  END LOOP;

  v_round_of_16_ids := ARRAY[]::uuid[];
  FOR v_i IN 1..8 LOOP
    INSERT INTO public.tournament_matches (tournament_id, round, bracket_position, next_match_id)
    VALUES (p_tournament_id, 'round_of_16', v_i, v_quarter_ids[((v_i - 1) / 2) + 1])
    RETURNING id INTO v_match_id;
    v_round_of_16_ids := v_round_of_16_ids || v_match_id;
  END LOOP;

  FOR v_group_index IN 0..3 LOOP
    v_group := CASE v_group_index WHEN 0 THEN 'A' WHEN 1 THEN 'B' WHEN 2 THEN 'C' ELSE 'D' END;
    FOR v_in_group IN 1..4 LOOP
      INSERT INTO public.tournament_matches (
        tournament_id, round, group_letter, bracket_position, next_match_id,
        player1_id, player2_id, status
      )
      VALUES (
        p_tournament_id,
        'group',
        v_group,
        v_in_group,
        v_round_of_16_ids[v_group_index * 2 + ((v_in_group - 1) / 2) + 1],
        v_shuffled[v_group_index * 8 + (v_in_group - 1) * 2 + 1],
        v_shuffled[v_group_index * 8 + (v_in_group - 1) * 2 + 2],
        'ready'
      );
    END LOOP;
  END LOOP;

  PERFORM public.schedule_tournament_matches(p_tournament_id);

  UPDATE public.tournaments
     SET status = 'awaiting_start', registration_enabled = false, updated_at = now()
   WHERE id = p_tournament_id
   RETURNING starts_at INTO v_start;

  INSERT INTO public.notifications (user_id, type, title, message, data, status)
  SELECT tp.user_id,
         'admin_announcement',
         'Tirage terminé — Groupe ' || tp.group_letter,
         'Vous êtes dans le Groupe ' || tp.group_letter || '. Votre premier match est programmé à partir du '
           || to_char(v_start AT TIME ZONE 'America/Port-au-Prince', 'DD/MM/YYYY à HH24:MI') || '.',
         jsonb_build_object(
           'tournament_id', p_tournament_id,
           'group', tp.group_letter,
           'kind', 'tournament_group',
           'starts_at', v_start,
           'timezone', 'America/Port-au-Prince'
         ),
         'unread'
    FROM public.tournament_participants tp
   WHERE tp.tournament_id = p_tournament_id;

  RETURN jsonb_build_object(
    'success', true,
    'total_matches', 32,
    'status', 'awaiting_start',
    'starts_at', v_start,
    'third_place_match_id', v_third_place_id,
    'auto_launch', p_auto
  );
END;
$$;

CREATE OR REPLACE FUNCTION public.advance_tournament_match_core(
  p_match_id uuid,
  p_winner_id uuid,
  p_score text DEFAULT NULL
)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_match public.tournament_matches%rowtype;
  v_next public.tournament_matches%rowtype;
  v_sibling public.tournament_matches%rowtype;
  v_third public.tournament_matches%rowtype;
  v_loser uuid;
  v_tournament public.tournaments%rowtype;
  v_rewards jsonb;
  v_amount numeric;
  v_auto_payout boolean := false;
  v_winner_name text;
  v_runner_name text;
  v_admin uuid;
BEGIN
  SELECT * INTO v_match
    FROM public.tournament_matches
   WHERE id = p_match_id
   FOR UPDATE;

  IF NOT FOUND THEN
    RAISE EXCEPTION 'match_not_found';
  END IF;
  IF v_match.status IN ('completed', 'walkover') THEN
    IF v_match.winner_id IS DISTINCT FROM p_winner_id THEN
      RAISE EXCEPTION 'tournament_match_already_resolved_with_a_different_winner';
    END IF;
    RETURN;
  END IF;
  IF p_winner_id IS NULL OR p_winner_id NOT IN (v_match.player1_id, v_match.player2_id) THEN
    RAISE EXCEPTION 'winner_not_in_match';
  END IF;

  v_loser := CASE
    WHEN p_winner_id = v_match.player1_id THEN v_match.player2_id
    ELSE v_match.player1_id
  END;

  UPDATE public.tournament_matches
     SET winner_id = p_winner_id,
         loser_id = v_loser,
         score = COALESCE(p_score, score),
         status = 'completed',
         played_at = now(),
         result_conflict = false,
         updated_at = now()
   WHERE id = p_match_id;

  IF v_match.round = 'semi' AND v_loser IS NOT NULL THEN
    SELECT * INTO v_third
      FROM public.tournament_matches
     WHERE tournament_id = v_match.tournament_id
       AND round = 'third_place'
     FOR UPDATE;

    IF FOUND THEN
      IF v_match.bracket_position = 1 THEN
        UPDATE public.tournament_matches
           SET player1_id = v_loser, updated_at = now()
         WHERE id = v_third.id;
      ELSE
        UPDATE public.tournament_matches
           SET player2_id = v_loser, updated_at = now()
         WHERE id = v_third.id;
      END IF;

      UPDATE public.tournament_matches
         SET status = CASE
           WHEN player1_id IS NOT NULL AND player2_id IS NOT NULL THEN 'ready'::public.tournament_match_status
           ELSE status
         END,
             updated_at = now()
       WHERE id = v_third.id;
    END IF;

    UPDATE public.tournament_participants
       SET status = 'active', eliminated_at_round = NULL, updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = v_loser;

    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    VALUES (
      v_loser, 'admin_announcement', 'Match pour la 3ème place',
      'Vous jouerez la petite finale pour déterminer le classement. Ce match ne verse pas de récompense.',
      jsonb_build_object('tournament_id', v_match.tournament_id, 'match_id', v_third.id, 'kind', 'tournament_third_place'),
      'unread'
    );
  ELSIF v_match.round = 'third_place' THEN
    UPDATE public.tournament_participants
       SET status = 'eliminated', final_rank = 3, eliminated_at_round = 'third_place', updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = p_winner_id;

    IF v_loser IS NOT NULL THEN
      UPDATE public.tournament_participants
         SET status = 'eliminated', final_rank = 4, eliminated_at_round = 'third_place', updated_at = now()
       WHERE tournament_id = v_match.tournament_id
         AND user_id = v_loser;
    END IF;

    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    VALUES (
      p_winner_id, 'admin_announcement', '3ème place confirmée',
      'Vous terminez troisième du tournoi. Aucune récompense financière n’est associée à cette place.',
      jsonb_build_object('tournament_id', v_match.tournament_id, 'rank', 3, 'kind', 'tournament_rank'),
      'unread'
    );
  ELSIF v_loser IS NOT NULL THEN
    UPDATE public.tournament_participants
       SET status = 'eliminated', eliminated_at_round = v_match.round, updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = v_loser;

    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    VALUES (
      v_loser, 'admin_announcement', 'Éliminé du tournoi',
      'Vous avez été éliminé au tour ' || v_match.round::text || '. Merci pour votre participation.',
      jsonb_build_object('tournament_id', v_match.tournament_id, 'kind', 'tournament_eliminated'),
      'unread'
    );
  END IF;

  IF v_match.round NOT IN ('final', 'third_place') THEN
    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    VALUES (
      p_winner_id, 'admin_announcement', 'Match remporté !',
      CASE WHEN v_match.round = 'semi'
        THEN 'Bravo, vous êtes qualifié pour la grande finale.'
        ELSE 'Bravo, vous passez au tour suivant du tournoi.'
      END,
      jsonb_build_object('tournament_id', v_match.tournament_id, 'kind', 'tournament_match_won'),
      'unread'
    );
  END IF;

  IF v_match.next_match_id IS NOT NULL THEN
    SELECT * INTO v_next
      FROM public.tournament_matches
     WHERE id = v_match.next_match_id
     FOR UPDATE;

    IF v_next.player1_id IS NULL AND v_next.player2_id IS DISTINCT FROM p_winner_id THEN
      UPDATE public.tournament_matches
         SET player1_id = p_winner_id, updated_at = now()
       WHERE id = v_match.next_match_id;
    ELSIF v_next.player2_id IS NULL AND v_next.player1_id IS DISTINCT FROM p_winner_id THEN
      UPDATE public.tournament_matches
         SET player2_id = p_winner_id, updated_at = now()
       WHERE id = v_match.next_match_id;
    END IF;

    SELECT * INTO v_next
      FROM public.tournament_matches
     WHERE id = v_match.next_match_id;

    IF v_next.player1_id IS NOT NULL
       AND v_next.player2_id IS NOT NULL
       AND v_next.status = 'pending' THEN
      UPDATE public.tournament_matches
         SET status = 'ready', updated_at = now()
       WHERE id = v_match.next_match_id;
    END IF;

    SELECT * INTO v_sibling
      FROM public.tournament_matches
     WHERE next_match_id = v_match.next_match_id
       AND id <> p_match_id
     LIMIT 1;

    IF v_sibling.id IS NOT NULL
       AND v_sibling.status = 'cancelled'
       AND v_next.status <> 'completed' THEN
      PERFORM public.advance_tournament_match_core(v_match.next_match_id, p_winner_id, 'BYE');
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      VALUES (
        p_winner_id, 'admin_announcement', 'Qualification automatique',
        'Votre adversaire a déclaré forfait. Vous êtes qualifié pour le tour suivant.',
        jsonb_build_object('tournament_id', v_match.tournament_id, 'match_id', v_match.next_match_id, 'kind', 'tournament_bye'),
        'unread'
      );
      RETURN;
    END IF;
  END IF;

  IF v_match.round = 'final' THEN
    SELECT * INTO v_tournament
      FROM public.tournaments
     WHERE id = v_match.tournament_id
     FOR UPDATE;
    v_rewards := COALESCE(v_tournament.rewards, '{}'::jsonb);

    SELECT COALESCE(lower(value) IN ('true', '1', 'on'), false)
      INTO v_auto_payout
      FROM public.platform_settings
     WHERE key = 'tournament_auto_payout';
    v_auto_payout := COALESCE(v_auto_payout, false);

    UPDATE public.tournaments
       SET status = 'completed', winner_id = p_winner_id, updated_at = now()
     WHERE id = v_match.tournament_id;

    UPDATE public.tournament_participants
       SET status = 'winner', final_rank = 1, updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = p_winner_id;

    IF v_loser IS NOT NULL THEN
      UPDATE public.tournament_participants
         SET status = 'eliminated', final_rank = 2, eliminated_at_round = 'final', updated_at = now()
       WHERE tournament_id = v_match.tournament_id
         AND user_id = v_loser;
    END IF;

    IF v_auto_payout THEN
      v_amount := COALESCE((v_rewards ->> 'first')::numeric, 0);
      IF v_amount > 0 THEN
        UPDATE public.wallets
           SET balance = balance + v_amount, updated_at = now()
         WHERE user_id = p_winner_id;
        INSERT INTO public.transactions (
          user_id, type, amount, balance_before, balance_after, description, is_sandbox
        )
        SELECT p_winner_id, 'tournament_prize', v_amount, balance - v_amount, balance,
               'Prix 1er — ' || v_tournament.name, false
          FROM public.wallets
         WHERE user_id = p_winner_id;
      END IF;

      v_amount := COALESCE((v_rewards ->> 'second')::numeric, 0);
      IF v_amount > 0 AND v_loser IS NOT NULL THEN
        UPDATE public.wallets
           SET balance = balance + v_amount, updated_at = now()
         WHERE user_id = v_loser;
        INSERT INTO public.transactions (
          user_id, type, amount, balance_before, balance_after, description, is_sandbox
        )
        SELECT v_loser, 'tournament_prize', v_amount, balance - v_amount, balance,
               'Prix 2e — ' || v_tournament.name, false
          FROM public.wallets
         WHERE user_id = v_loser;
      END IF;

      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      VALUES (
        p_winner_id, 'admin_announcement', '🏆 Champion du tournoi !',
        'Félicitations, vous remportez « ' || v_tournament.name || ' ». Votre prix a été crédité sur votre portefeuille.',
        jsonb_build_object('tournament_id', v_match.tournament_id, 'kind', 'tournament_champion'),
        'unread'
      );
    ELSE
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      VALUES (
        p_winner_id, 'admin_announcement', '🏆 Champion du tournoi !',
        'Félicitations, vous remportez « ' || v_tournament.name || ' » ! L’équipe Mindspille vous transférera votre récompense.',
        jsonb_build_object('tournament_id', v_match.tournament_id, 'kind', 'tournament_champion'),
        'unread'
      );

      SELECT username INTO v_winner_name FROM public.profiles WHERE id = p_winner_id;
      SELECT username INTO v_runner_name FROM public.profiles WHERE id = v_loser;

      FOR v_admin IN
        SELECT user_id FROM public.user_roles WHERE role IN ('admin', 'super_admin')
      LOOP
        INSERT INTO public.notifications (user_id, type, title, message, data, status)
        VALUES (
          v_admin, 'admin_warning', '🏆 Tournoi terminé — versement manuel requis',
          'Tournoi « ' || v_tournament.name || ' » : 1er ' || COALESCE(v_winner_name, '?')
            || ' (' || COALESCE(v_rewards ->> 'first', '0') || ' HTG)'
            || CASE WHEN v_loser IS NOT NULL
                 THEN ', 2e ' || COALESCE(v_runner_name, '?') || ' (' || COALESCE(v_rewards ->> 'second', '0') || ' HTG)'
                 ELSE '' END
            || '. Aucun portefeuille n’a été crédité : transférez les prix manuellement.',
          jsonb_build_object(
            'tournament_id', v_match.tournament_id,
            'kind', 'tournament_manual_payout',
            'winner_id', p_winner_id,
            'runner_up_id', v_loser,
            'rewards', v_rewards
          ),
          'unread'
        );
      END LOOP;
    END IF;
  END IF;
END;
$$;

-- Keep the administrator path and the trusted game-server path on the exact
-- same advancement logic, avoiding divergent payouts or rankings.
CREATE OR REPLACE FUNCTION public.advance_tournament_match_internal(
  p_match_id uuid,
  p_winner_id uuid,
  p_score text DEFAULT NULL
)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
BEGIN
  PERFORM public.advance_tournament_match_core(p_match_id, p_winner_id, p_score);
END;
$$;

REVOKE ALL ON FUNCTION public.advance_tournament_match_core(uuid, uuid, text) FROM PUBLIC, anon, authenticated;
REVOKE ALL ON FUNCTION public.advance_tournament_match_internal(uuid, uuid, text) FROM PUBLIC, anon, authenticated;

CREATE OR REPLACE FUNCTION public.run_tournament_scheduler()
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path = public, pg_temp
AS $$
DECLARE
  v_tournament record;
  v_match record;
  v_participant_count integer;
  v_draw_warnings integer := 0;
  v_brackets_published integer := 0;
  v_started integer := 0;
  v_reopened_draws integer := 0;
  v_match_reminders integer := 0;
  v_forfeits jsonb := '{}'::jsonb;
BEGIN
  FOR v_tournament IN
    SELECT id, name, starts_at
      FROM public.tournaments
     WHERE status = 'drawing'
       AND draw_notified_5min = false
       AND draw_ends_at > now()
       AND draw_ends_at <= now() + interval '5 minutes'
     FOR UPDATE SKIP LOCKED
  LOOP
    UPDATE public.tournaments
       SET draw_notified_5min = true, updated_at = now()
     WHERE id = v_tournament.id
       AND draw_notified_5min = false;

    IF FOUND THEN
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      SELECT tp.user_id,
             'admin_announcement',
             '⏳ Résultat du tirage dans 5 minutes',
             'Les groupes du tournoi « ' || v_tournament.name || ' » seront publiés dans 5 minutes. Le premier match reste programmé à 09h00.',
             jsonb_build_object('tournament_id', v_tournament.id, 'kind', 'tournament_draw_ending_soon', 'starts_at', v_tournament.starts_at),
             'unread'
        FROM public.tournament_participants tp
       WHERE tp.tournament_id = v_tournament.id
         AND tp.status = 'active';
      v_draw_warnings := v_draw_warnings + 1;
    END IF;
  END LOOP;

  FOR v_tournament IN
    SELECT id, auto_launch
      FROM public.tournaments
     WHERE status = 'drawing'
       AND draw_ends_at IS NOT NULL
       AND draw_ends_at <= now()
     FOR UPDATE SKIP LOCKED
  LOOP
    SELECT count(*) INTO v_participant_count
      FROM public.tournament_participants
     WHERE tournament_id = v_tournament.id
       AND status = 'active';

    IF v_participant_count = 32 THEN
      BEGIN
        PERFORM public.launch_tournament(v_tournament.id, COALESCE(v_tournament.auto_launch, true));
        v_brackets_published := v_brackets_published + 1;
      EXCEPTION WHEN others THEN
        INSERT INTO public.admin_logs (admin_id, action, details)
        SELECT ur.user_id,
               'tournament_scheduler_error',
               jsonb_build_object('tournament_id', v_tournament.id, 'error', SQLERRM)
          FROM public.user_roles ur
         WHERE ur.role IN ('admin', 'super_admin');
      END;
    ELSE
      UPDATE public.tournaments
         SET status = 'registration_open',
             registration_enabled = true,
             draw_started_at = NULL,
             draw_ends_at = NULL,
             draw_notified_5min = false,
             starts_at = NULL,
             updated_at = now()
       WHERE id = v_tournament.id;

      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      SELECT tp.user_id,
             'admin_announcement',
             'Inscriptions du tournoi rouvertes',
             'Le nombre de participants a changé avant la fin du tirage. Les inscriptions restent ouvertes jusqu’à ce que le tableau soit complet.',
             jsonb_build_object('tournament_id', v_tournament.id, 'kind', 'tournament_registration_reopened'),
             'unread'
        FROM public.tournament_participants tp
       WHERE tp.tournament_id = v_tournament.id
         AND tp.status = 'active';
      v_reopened_draws := v_reopened_draws + 1;
    END IF;
  END LOOP;

  FOR v_tournament IN
    SELECT id, name, starts_at
      FROM public.tournaments
     WHERE status = 'awaiting_start'
       AND auto_launch = true
       AND starts_at IS NOT NULL
       AND starts_at <= now()
     FOR UPDATE SKIP LOCKED
  LOOP
    UPDATE public.tournaments
       SET status = 'in_progress', updated_at = now()
     WHERE id = v_tournament.id
       AND status = 'awaiting_start';

    IF FOUND THEN
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      SELECT tp.user_id,
             'admin_announcement',
             '🏁 Le tournoi commence',
             'Le tournoi « ' || v_tournament.name || ' » est lancé. Respectez l’horaire indiqué pour votre match.',
             jsonb_build_object('tournament_id', v_tournament.id, 'kind', 'tournament_started', 'starts_at', v_tournament.starts_at),
             'unread'
        FROM public.tournament_participants tp
       WHERE tp.tournament_id = v_tournament.id
         AND tp.status = 'active';
      v_started := v_started + 1;
    END IF;
  END LOOP;

  FOR v_match IN
    SELECT id, tournament_id, player1_id, player2_id, scheduled_at
      FROM public.tournament_matches
     WHERE status IN ('pending', 'ready')
       AND reminder_notified_5min = false
       AND scheduled_at >= now() + interval '4 minutes'
       AND scheduled_at <= now() + interval '6 minutes'
     FOR UPDATE SKIP LOCKED
  LOOP
    UPDATE public.tournament_matches
       SET reminder_notified_5min = true, updated_at = now()
     WHERE id = v_match.id
       AND reminder_notified_5min = false;

    IF FOUND THEN
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      SELECT player_id,
             'admin_announcement',
             '⚽ Votre match commence dans 5 min',
             'Rendez-vous à ' || to_char(v_match.scheduled_at AT TIME ZONE 'America/Port-au-Prince', 'HH24:MI') || ' pour votre match de tournoi.',
             jsonb_build_object('tournament_id', v_match.tournament_id, 'match_id', v_match.id, 'kind', 'tournament_match_reminder'),
             'unread'
        FROM unnest(ARRAY[v_match.player1_id, v_match.player2_id]) AS player_id
       WHERE player_id IS NOT NULL;
      v_match_reminders := v_match_reminders + 1;
    END IF;
  END LOOP;

  v_forfeits := COALESCE(public.process_tournament_forfeits(), '{}'::jsonb);

  RETURN jsonb_build_object(
    'ok', true,
    'draw_warnings', v_draw_warnings,
    'brackets_published', v_brackets_published,
    'started_at_09', v_started,
    'reopened_incomplete_draws', v_reopened_draws,
    'match_reminders', v_match_reminders,
    'forfeits', v_forfeits
  );
END;
$$;

REVOKE ALL ON FUNCTION public.run_tournament_scheduler() FROM PUBLIC, anon, authenticated;
GRANT EXECUTE ON FUNCTION public.run_tournament_scheduler() TO service_role;
