-- LE TABLEAU FINAL : CROISEMENT DES GROUPES ET PETITE FINALE
--
-- Deux défauts distincts, dans la même chaîne.
--
-- 1. Les huitièmes opposaient des qualifiés du MÊME groupe. Les quatre matchs
--    d'un groupe alimentaient deux huitièmes de ce groupe : le vainqueur du
--    match 1 du groupe A affrontait celui du match 2 du groupe A. Un tournoi
--    croise les groupes — A contre B, C contre D, et en classement inversé.
--
-- 2. Le vainqueur allait « à la première place libre » du match suivant. Deux
--    matchs qui alimentent la même case n'ont alors aucun ordre garanti : c'est
--    celui qui finit le premier qui s'assied à gauche. Chaque match sait
--    désormais quelle place il alimente, et c'est la seule qu'il occupe.
--
-- 3. La petite finale se remplissait dès la première demi-finale terminée, et
--    la finale aussi. Les deux matchs restent vides tant que les DEUX
--    demi-finales n'ont pas rendu leur verdict, puis se remplissent ensemble :
--    les deux vainqueurs en finale, les deux perdants en petite finale.
--
-- Le classement final ne change pas : 1er le vainqueur de la finale, 2e son
-- adversaire, 3e le vainqueur de la petite finale, 4e son adversaire.

-- ══════════════════════════════════════════════════════════════════════════
--  La place qu'un match alimente dans le tour suivant
-- ══════════════════════════════════════════════════════════════════════════
-- Une seule source de vérité, utilisée aussi bien pour asseoir un vainqueur
-- que pour marquer une place vacante — sinon un forfait réserverait une case
-- et le vainqueur légitime en trouverait une autre.
--
-- Huitièmes : A1-B4, A2-B3, A3-B2, A4-B1, puis C1-D4, C2-D3, C3-D2, C4-D1.
-- Les groupes A et C tiennent la place de gauche, B et D celle de droite.
CREATE OR REPLACE FUNCTION public.tournament_feeder_slot(
  p_round public.tournament_round,
  p_group_letter char(1),
  p_bracket_position integer
)
RETURNS integer
LANGUAGE sql
IMMUTABLE
AS $function$
  SELECT CASE p_round
    WHEN 'group' THEN CASE WHEN p_group_letter IN ('A', 'C') THEN 1 ELSE 2 END
    WHEN 'round_of_16' THEN CASE WHEN p_bracket_position % 2 = 1 THEN 1 ELSE 2 END
    WHEN 'quarter' THEN CASE WHEN p_bracket_position % 2 = 1 THEN 1 ELSE 2 END
    WHEN 'semi' THEN CASE WHEN p_bracket_position = 1 THEN 1 ELSE 2 END
    ELSE NULL
  END;
$function$;

COMMENT ON FUNCTION public.tournament_feeder_slot(public.tournament_round, char, integer) IS
  'Place (1 ou 2) qu''un match occupe dans le tour suivant. Groupes A et C à gauche, B et D à droite ; ensuite, position impaire à gauche.';

-- ══════════════════════════════════════════════════════════════════════════
--  Finale et petite finale : remplies ensemble, jamais avant
-- ══════════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION public.fill_tournament_finals_if_ready(p_tournament_id uuid)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_semi1 public.tournament_matches%rowtype;
  v_semi2 public.tournament_matches%rowtype;
  v_final public.tournament_matches%rowtype;
  v_third public.tournament_matches%rowtype;
  v_filled_final boolean := false;
  v_filled_third boolean := false;
BEGIN
  SELECT * INTO v_semi1
    FROM public.tournament_matches
   WHERE tournament_id = p_tournament_id AND round = 'semi' AND bracket_position = 1
   FOR UPDATE;
  SELECT * INTO v_semi2
    FROM public.tournament_matches
   WHERE tournament_id = p_tournament_id AND round = 'semi' AND bracket_position = 2
   FOR UPDATE;

  IF v_semi1.id IS NULL OR v_semi2.id IS NULL THEN
    RETURN jsonb_build_object('status', 'semis_missing');
  END IF;

  -- Le verdict des DEUX demi-finales, ou rien. Une seule demi-finale terminée
  -- ne dit ni qui joue la finale, ni qui joue la petite finale.
  IF NOT (v_semi1.status IN ('completed', 'walkover') AND v_semi1.winner_id IS NOT NULL
      AND v_semi2.status IN ('completed', 'walkover') AND v_semi2.winner_id IS NOT NULL) THEN
    RETURN jsonb_build_object('status', 'waiting_for_both_semis');
  END IF;

  -- ── FINALE : les deux vainqueurs ────────────────────────────────────────
  SELECT * INTO v_final
    FROM public.tournament_matches
   WHERE tournament_id = p_tournament_id AND round = 'final'
   FOR UPDATE;

  IF v_final.id IS NOT NULL
     AND v_final.status NOT IN ('completed', 'walkover', 'cancelled')
     AND v_final.game_id IS NULL THEN
    UPDATE public.tournament_matches
       SET player1_id = v_semi1.winner_id,
           player2_id = v_semi2.winner_id,
           player1_slot_vacant = false,
           player2_slot_vacant = false,
           status = CASE WHEN status = 'pending' THEN 'ready'::public.tournament_match_status ELSE status END,
           updated_at = now()
     WHERE id = v_final.id
       AND (player1_id IS DISTINCT FROM v_semi1.winner_id
         OR player2_id IS DISTINCT FROM v_semi2.winner_id);
    v_filled_final := FOUND;
  END IF;

  -- ── PETITE FINALE : les deux perdants ───────────────────────────────────
  SELECT * INTO v_third
    FROM public.tournament_matches
   WHERE tournament_id = p_tournament_id AND round = 'third_place'
   FOR UPDATE;

  IF v_third.id IS NOT NULL
     AND v_third.status NOT IN ('completed', 'walkover', 'cancelled')
     AND v_third.game_id IS NULL THEN
    -- Une demi-finale gagnée contre une place vacante n'a pas de perdant :
    -- la case reste déclarée vacante plutôt que vide, pour que la machinerie
    -- de forfait existante sache quoi en faire.
    UPDATE public.tournament_matches
       SET player1_id = v_semi1.loser_id,
           player2_id = v_semi2.loser_id,
           player1_slot_vacant = (v_semi1.loser_id IS NULL),
           player2_slot_vacant = (v_semi2.loser_id IS NULL),
           status = CASE WHEN status = 'pending' THEN 'ready'::public.tournament_match_status ELSE status END,
           updated_at = now()
     WHERE id = v_third.id
       AND (player1_id IS DISTINCT FROM v_semi1.loser_id
         OR player2_id IS DISTINCT FROM v_semi2.loser_id);
    v_filled_third := FOUND;
  END IF;

  -- Les deux perdants restent en lice : il leur reste un match à jouer.
  IF v_filled_third THEN
    UPDATE public.tournament_participants
       SET status = 'active', eliminated_at_round = NULL, updated_at = now()
     WHERE tournament_id = p_tournament_id
       AND user_id IN (v_semi1.loser_id, v_semi2.loser_id);

    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    SELECT player_id, 'admin_announcement', 'Match pour la 3ème place',
           'Vous jouerez la petite finale pour déterminer le classement. Ce match ne verse pas de récompense.',
           jsonb_build_object('tournament_id', p_tournament_id, 'match_id', v_third.id,
                              'kind', 'tournament_third_place',
                              'url', '/tournament-match/' || v_third.id::text),
           'unread'
      FROM unnest(ARRAY[v_semi1.loser_id, v_semi2.loser_id]) AS player_id
     WHERE player_id IS NOT NULL;
  END IF;

  IF v_filled_final THEN
    INSERT INTO public.notifications (user_id, type, title, message, data, status)
    SELECT player_id, 'admin_announcement', '🏁 Vous êtes en finale',
           'Votre adversaire de la grande finale est connu. Rendez-vous à l''heure prévue.',
           jsonb_build_object('tournament_id', p_tournament_id, 'match_id', v_final.id,
                              'kind', 'tournament_final_ready',
                              'url', '/tournament-match/' || v_final.id::text),
           'unread'
      FROM unnest(ARRAY[v_semi1.winner_id, v_semi2.winner_id]) AS player_id
     WHERE player_id IS NOT NULL;
  END IF;

  RETURN jsonb_build_object(
    'status', 'filled',
    'final_filled', v_filled_final,
    'third_place_filled', v_filled_third,
    'final_players', jsonb_build_array(v_semi1.winner_id, v_semi2.winner_id),
    'third_place_players', jsonb_build_array(v_semi1.loser_id, v_semi2.loser_id)
  );
END;
$function$;

REVOKE ALL ON FUNCTION public.fill_tournament_finals_if_ready(uuid) FROM PUBLIC, anon, authenticated;

COMMENT ON FUNCTION public.fill_tournament_finals_if_ready(uuid) IS
  'Remplit la finale (les deux vainqueurs) et la petite finale (les deux perdants) une fois les DEUX demi-finales terminées. Idempotente.';

-- ══════════════════════════════════════════════════════════════════════════
--  Avancement du tableau
-- ══════════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION public.advance_tournament_match_core(
  p_match_id uuid,
  p_winner_id uuid,
  p_score text DEFAULT NULL::text
)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_match public.tournament_matches%rowtype;
  v_next public.tournament_matches%rowtype;
  v_sibling public.tournament_matches%rowtype;
  v_loser uuid;
  v_tournament public.tournaments%rowtype;
  v_rewards jsonb;
  v_amount numeric;
  v_auto_payout boolean := false;
  v_winner_name text;
  v_runner_name text;
  v_admin uuid;
  v_took_vacant_slot boolean := false;
  v_target_slot integer;
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
         -- Ce match a un vainqueur : il ne propage plus aucune vacance.
         vacancy_propagated_at = NULL,
         updated_at = now()
   WHERE id = p_match_id;

  -- Un joueur peut avoir ete elimine par un double forfait tranche plus tard en
  -- sa faveur. Gagner son match le remet dans le tournoi.
  IF v_match.round NOT IN ('final', 'third_place') THEN
    UPDATE public.tournament_participants
       SET status = 'active', eliminated_at_round = NULL, updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = p_winner_id
       AND status = 'eliminated';
  END IF;

  IF v_match.round = 'semi' THEN
    -- Le perdant d'une demi-finale n'est pas eliminé : il lui reste la petite
    -- finale. Sa place y sera attribuée quand l'AUTRE demi-finale aura rendu
    -- son verdict — pas avant, sinon le tableau annonce un match dont on ne
    -- connaît qu'un joueur.
    UPDATE public.tournament_participants
       SET status = 'active', eliminated_at_round = NULL, updated_at = now()
     WHERE tournament_id = v_match.tournament_id
       AND user_id = v_loser;

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
      'Vous terminez troisième du tournoi. Aucune récompense financière n''est associée à cette place.',
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

  -- ── PROPAGATION ────────────────────────────────────────────────────────
  IF v_match.round = 'semi' THEN
    -- Finale et petite finale se remplissent ensemble, une fois les deux
    -- demi-finales jouées. Rien ne descend d'une demi-finale isolée.
    PERFORM public.fill_tournament_finals_if_ready(v_match.tournament_id);

  ELSIF v_match.next_match_id IS NOT NULL THEN
    SELECT * INTO v_next
      FROM public.tournament_matches
     WHERE id = v_match.next_match_id
     FOR UPDATE;

    -- On ne touche jamais a un tour suivant deja lance ou deja tranche.
    IF v_next.id IS NOT NULL
       AND v_next.status NOT IN ('completed', 'walkover', 'cancelled')
       AND v_next.game_id IS NULL
       AND v_next.player1_id IS DISTINCT FROM p_winner_id
       AND v_next.player2_id IS DISTINCT FROM p_winner_id THEN

      v_target_slot := public.tournament_feeder_slot(
        v_match.round, v_match.group_letter, v_match.bracket_position);

      -- Sa place est reservee d'avance : c'est celle-la qu'il prend, libre ou
      -- declaree vacante. Prendre « la premiere libre » faisait s'affronter
      -- deux qualifies du meme groupe.
      IF v_target_slot = 1 AND v_next.player1_id IS NULL THEN
        v_took_vacant_slot := COALESCE(v_next.player1_slot_vacant, false);
        UPDATE public.tournament_matches
           SET player1_id = p_winner_id, player1_slot_vacant = false, updated_at = now()
         WHERE id = v_next.id;

      ELSIF v_target_slot = 2 AND v_next.player2_id IS NULL THEN
        v_took_vacant_slot := COALESCE(v_next.player2_slot_vacant, false);
        UPDATE public.tournament_matches
           SET player2_id = p_winner_id, player2_slot_vacant = false, updated_at = now()
         WHERE id = v_next.id;

      -- Repli : sa place est occupee par un autre. Le tableau est incoherent,
      -- mais on ne perd pas le vainqueur pour autant — il prend la place
      -- restante et l'incoherence est signalee.
      ELSIF v_next.player1_id IS NULL THEN
        v_took_vacant_slot := COALESCE(v_next.player1_slot_vacant, false);
        UPDATE public.tournament_matches
           SET player1_id = p_winner_id, player1_slot_vacant = false,
               result_conflict = true, updated_at = now()
         WHERE id = v_next.id;

      ELSIF v_next.player2_id IS NULL THEN
        v_took_vacant_slot := COALESCE(v_next.player2_slot_vacant, false);
        UPDATE public.tournament_matches
           SET player2_id = p_winner_id, player2_slot_vacant = false,
               result_conflict = true, updated_at = now()
         WHERE id = v_next.id;

      ELSE
        UPDATE public.tournament_matches
           SET result_conflict = true, updated_at = now()
         WHERE id = v_next.id;
      END IF;
    END IF;

    SELECT * INTO v_next
      FROM public.tournament_matches
     WHERE id = v_match.next_match_id;

    IF (v_next.player1_id IS NOT NULL OR v_next.player1_slot_vacant)
       AND (v_next.player2_id IS NOT NULL OR v_next.player2_slot_vacant)
       AND v_next.status = 'pending' THEN
      UPDATE public.tournament_matches
         SET status = 'ready', updated_at = now()
       WHERE id = v_match.next_match_id;
    END IF;

    -- L'adversaire croyait passer sans jouer : il faut le lui dire.
    IF v_took_vacant_slot THEN
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      SELECT other_id, 'admin_announcement', 'Votre prochain match a un adversaire',
             'La place vacante de votre prochain match vient d''être pourvue : '
               || 'le vainqueur de l''autre rencontre a été désigné. Vous jouerez ce match.',
             jsonb_build_object(
               'tournament_id', v_match.tournament_id,
               'match_id', v_next.id,
               'kind', 'tournament_vacancy_filled',
               'url', '/tournament-match/' || v_next.id::text
             ),
             'unread'
        FROM (SELECT CASE WHEN v_next.player1_id = p_winner_id
                          THEN v_next.player2_id ELSE v_next.player1_id END AS other_id) s
       WHERE other_id IS NOT NULL;
    END IF;

    SELECT * INTO v_sibling
      FROM public.tournament_matches
     WHERE next_match_id = v_match.next_match_id
       AND id <> p_match_id
     LIMIT 1;

    IF v_sibling.id IS NOT NULL
       AND v_sibling.status = 'cancelled'
       AND v_next.status NOT IN ('completed', 'walkover') THEN
      INSERT INTO public.notifications (user_id, type, title, message, data, status)
      VALUES (
        p_winner_id, 'admin_announcement', 'Qualification par forfait possible',
        'Une place est vacante dans votre prochain match. Confirmez votre présence pendant le créneau prévu pour valider votre qualification.',
        jsonb_build_object(
          'tournament_id', v_match.tournament_id,
          'match_id', v_match.next_match_id,
          'kind', 'tournament_vacant_opponent',
          'url', '/tournament-match/' || v_match.next_match_id::text
        ),
        'unread'
      );
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
        'Félicitations, vous remportez « ' || v_tournament.name || ' » ! L''équipe Mindspille vous transférera votre récompense.',
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
            || '. Aucun portefeuille n''a été crédité : transférez les prix manuellement.',
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
$function$;

-- ══════════════════════════════════════════════════════════════════════════
--  Une vacance se marque à la place que le match aurait occupée
-- ══════════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION private.propagate_tournament_vacancy(p_match_id uuid)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO ''
AS $function$
declare
  v_match public.tournament_matches%rowtype;
  v_next public.tournament_matches%rowtype;
  v_candidate uuid;
  v_child jsonb;
  v_slot integer;
begin
  select * into v_match
  from public.tournament_matches
  where id = p_match_id
  for update;

  if not found then
    raise exception 'match_not_found';
  end if;
  if v_match.winner_id is not null then
    return jsonb_build_object('status', 'winner_already_present', 'match_id', v_match.id);
  end if;
  if v_match.vacancy_propagated_at is not null then
    return jsonb_build_object('status', 'already_propagated', 'match_id', v_match.id);
  end if;
  if v_match.status <> 'cancelled' then
    return jsonb_build_object('status', 'not_cancelled', 'match_id', v_match.id);
  end if;

  if v_match.next_match_id is null then
    update public.tournament_matches
       set vacancy_propagated_at = now(), updated_at = now()
     where id = v_match.id;

    if v_match.round = 'final' then
      insert into public.notifications (user_id, type, title, message, data, status)
      select tp.user_id, 'admin_announcement', 'Tournoi clôturé sans champion',
             'Aucun finaliste ne s’est présenté. Le tournoi est annulé et les sommes encore bloquées seront remboursées.',
             jsonb_build_object(
               'tournament_id', v_match.tournament_id,
               'match_id', v_match.id,
               'kind', 'tournament_no_eligible_finalist'
             ),
             'unread'
        from public.tournament_participants tp
       where tp.tournament_id = v_match.tournament_id
         and tp.status in ('active', 'winner');

      insert into public.notifications (user_id, type, title, message, data, status)
      select ur.user_id, 'admin_warning', 'Tournoi annulé — aucun finaliste',
             'Le bracket a été clôturé sans champion car aucune place éligible n’est arrivée en finale.',
             jsonb_build_object(
               'tournament_id', v_match.tournament_id,
               'match_id', v_match.id,
               'kind', 'tournament_no_eligible_finalist'
             ),
             'unread'
        from public.user_roles ur
       where ur.role in ('admin', 'super_admin');

      update public.tournament_participants
         set status = 'eliminated', updated_at = now()
       where tournament_id = v_match.tournament_id
         and status in ('active', 'winner');

      update public.tournaments
         set status = 'cancelled',
             winner_id = null,
             completion_reason = 'no_eligible_finalist',
             updated_at = now()
       where id = v_match.tournament_id
         and status in ('awaiting_start', 'in_progress');
    end if;

    return jsonb_build_object('status', 'terminal_vacancy', 'match_id', v_match.id);
  end if;

  select * into v_next
  from public.tournament_matches
  where id = v_match.next_match_id
  for update;

  if not found then
    update public.tournament_matches
       set result_conflict = true, updated_at = now()
     where id = v_match.id;
    return jsonb_build_object('status', 'next_match_missing', 'match_id', v_match.id);
  end if;

  if v_next.status in ('completed', 'walkover') then
    update public.tournament_matches
       set vacancy_propagated_at = now(), updated_at = now()
     where id = v_match.id;
    return jsonb_build_object('status', 'downstream_already_resolved', 'match_id', v_match.id);
  end if;

  if v_next.status = 'cancelled' and v_next.winner_id is null then
    update public.tournament_matches
       set vacancy_propagated_at = now(), updated_at = now()
     where id = v_match.id;
    v_child := private.propagate_tournament_vacancy(v_next.id);
    return jsonb_build_object('status', 'continued_from_cancelled', 'child', v_child);
  end if;

  if v_next.status = 'in_progress' or v_next.game_id is not null then
    update public.tournament_matches
       set result_conflict = true, updated_at = now()
     where id in (v_match.id, v_next.id);
    return jsonb_build_object('status', 'downstream_already_started', 'match_id', v_match.id);
  end if;

  -- La vacance se marque a la place que ce match alimente, exactement comme
  -- l'aurait fait son vainqueur. Sans cela, un forfait reserve une case et le
  -- vainqueur legitime de l'autre branche en trouve une autre.
  v_slot := public.tournament_feeder_slot(
    v_match.round, v_match.group_letter, v_match.bracket_position);

  if v_slot = 1 and v_next.player1_id is null and not v_next.player1_slot_vacant then
    update public.tournament_matches
       set player1_slot_vacant = true, updated_at = now()
     where id = v_next.id;
  elsif v_slot = 2 and v_next.player2_id is null and not v_next.player2_slot_vacant then
    update public.tournament_matches
       set player2_slot_vacant = true, updated_at = now()
     where id = v_next.id;
  elsif v_next.player1_id is null and not v_next.player1_slot_vacant then
    update public.tournament_matches
       set player1_slot_vacant = true, updated_at = now()
     where id = v_next.id;
  elsif v_next.player2_id is null and not v_next.player2_slot_vacant then
    update public.tournament_matches
       set player2_slot_vacant = true, updated_at = now()
     where id = v_next.id;
  else
    update public.tournament_matches
       set result_conflict = true, updated_at = now()
     where id = v_match.id;
    return jsonb_build_object('status', 'no_downstream_slot_available', 'match_id', v_match.id);
  end if;

  update public.tournament_matches
     set vacancy_propagated_at = now(), updated_at = now()
   where id = v_match.id;

  select * into v_next
  from public.tournament_matches
  where id = v_match.next_match_id
  for update;

  if (v_next.player1_id is not null or v_next.player1_slot_vacant)
     and (v_next.player2_id is not null or v_next.player2_slot_vacant) then
    if v_next.player1_slot_vacant and v_next.player2_slot_vacant then
      update public.tournament_matches
         set status = 'cancelled',
             score = 'DOUBLE_FORFAIT',
             played_at = coalesce(played_at, now()),
             forfeit_processed = true,
             updated_at = now()
       where id = v_next.id;

      v_child := private.propagate_tournament_vacancy(v_next.id);
      return jsonb_build_object('status', 'double_vacancy_propagated', 'child', v_child);
    end if;

    v_candidate := case
      when v_next.player1_slot_vacant then v_next.player2_id
      when v_next.player2_slot_vacant then v_next.player1_id
      else null
    end;

    update public.tournament_matches
       set status = case
             when status = 'pending' then 'ready'::public.tournament_match_status
             else status
           end,
           updated_at = now()
     where id = v_next.id;

    if v_candidate is not null then
      insert into public.notifications (user_id, type, title, message, data, status)
      values (
        v_candidate,
        'admin_announcement',
        'Qualification par forfait possible',
        'Votre adversaire est absent. Confirmez votre présence pendant le créneau du match pour valider votre qualification.',
        jsonb_build_object(
          'tournament_id', v_next.tournament_id,
          'match_id', v_next.id,
          'kind', 'tournament_vacant_opponent',
          'scheduled_at', v_next.scheduled_at,
          'url', '/tournament-match/' || v_next.id::text
        ),
        'unread'
      );
    end if;
  end if;

  return jsonb_build_object('status', 'vacancy_propagated', 'match_id', v_match.id, 'next_match_id', v_next.id);
end;
$function$;

-- ══════════════════════════════════════════════════════════════════════════
--  Construction du tableau : les groupes se croisent
-- ══════════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION public.launch_tournament(p_tournament_id uuid, p_auto boolean DEFAULT true)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
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
  v_end timestamptz;
  v_tz text;
BEGIN
  IF NOT public.is_tournament_operator() THEN
    RAISE EXCEPTION 'forbidden';
  END IF;

  SELECT status, coalesce(nullif(tournament_timezone, ''), 'America/Port-au-Prince')
    INTO v_current_status, v_tz
    FROM public.tournaments
   WHERE id = p_tournament_id
   FOR UPDATE;
  IF NOT FOUND THEN
    RAISE EXCEPTION 'tournament_not_found';
  END IF;

  -- Le tableau ne se construit qu'une fois. Relancer ne recree rien.
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

  -- La petite finale ne pointe vers rien : elle ne fait avancer personne, elle
  -- departage la 3e et la 4e place. Elle est alimentee par les PERDANTS des
  -- demi-finales, ce qu'aucun `next_match_id` ne saurait exprimer.
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
        -- Les groupes se croisent, en classement inverse :
        --   A1-B4  A2-B3  A3-B2  A4-B1   puis   C1-D4  C2-D3  C3-D2  C4-D1
        -- Auparavant les quatre matchs d'un groupe alimentaient deux huitiemes
        -- de ce meme groupe : deux qualifies du groupe A s'affrontaient des les
        -- huitiemes, et la moitie du tableau ne rencontrait jamais l'autre.
        v_round_of_16_ids[
          CASE v_group_index
            WHEN 0 THEN v_in_group          -- A1→1  A2→2  A3→3  A4→4
            WHEN 1 THEN 5 - v_in_group      -- B1→4  B2→3  B3→2  B4→1
            WHEN 2 THEN 4 + v_in_group      -- C1→5  C2→6  C3→7  C4→8
            ELSE 9 - v_in_group             -- D1→8  D2→7  D3→6  D4→5
          END
        ],
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
   RETURNING starts_at, estimated_ends_at INTO v_start, v_end;

  -- Chaque joueur reçoit SON calendrier : groupe, début officiel du tournoi,
  -- date et heure exactes de son premier match, et fin prévue.
  INSERT INTO public.notifications (user_id, type, title, message, data, status)
  SELECT tp.user_id,
         'admin_announcement',
         'Tirage terminé — Groupe ' || tp.group_letter,
         'Vous êtes dans le Groupe ' || tp.group_letter || '. '
           || 'Le tournoi commence le '
           || to_char(v_start AT TIME ZONE v_tz, 'DD/MM/YYYY à HH24:MI')
           || case
                when fm.scheduled_at is not null
                then '. Votre premier match est programmé le '
                     || to_char(fm.scheduled_at AT TIME ZONE v_tz, 'DD/MM/YYYY à HH24:MI')
                else ''
              end
           || case
                when v_end is not null
                then '. Fin prévue le ' || to_char(v_end AT TIME ZONE v_tz, 'DD/MM/YYYY')
                else ''
              end
           || ' (heure d''Haïti). Vous avez 1 heure après l''horaire pour rejoindre votre match.',
         jsonb_build_object(
           'tournament_id', p_tournament_id,
           'group', tp.group_letter,
           'kind', 'tournament_group',
           'starts_at', v_start,
           'estimated_ends_at', v_end,
           'first_match_id', fm.id,
           'first_match_at', fm.scheduled_at,
           'timezone', v_tz
         ),
         'unread'
    FROM public.tournament_participants tp
    LEFT JOIN LATERAL (
      SELECT tm.id, tm.scheduled_at
        FROM public.tournament_matches tm
       WHERE tm.tournament_id = p_tournament_id
         AND (tm.player1_id = tp.user_id OR tm.player2_id = tp.user_id)
         AND tm.scheduled_at IS NOT NULL
       ORDER BY tm.scheduled_at
       LIMIT 1
    ) fm ON true
   WHERE tp.tournament_id = p_tournament_id;

  RETURN jsonb_build_object(
    'success', true,
    'total_matches', 32,
    'status', 'awaiting_start',
    'starts_at', v_start,
    'estimated_ends_at', v_end,
    'third_place_match_id', v_third_place_id,
    'auto_launch', p_auto
  );
END;
$function$;
