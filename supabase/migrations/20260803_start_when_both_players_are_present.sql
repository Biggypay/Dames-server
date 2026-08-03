-- LE MATCH COMMENCE QUAND LES DEUX JOUEURS SONT LÀ
--
-- L'horaire officiel servait de barrière : impossible de confirmer sa présence
-- plus de cinq minutes avant, et impossible d'ouvrir le plateau avant l'heure
-- pile — même quand les deux joueurs étaient devant leur écran, prêts, à se
-- regarder attendre. Un créneau est un rendez-vous, pas une obligation.
--
-- Désormais : la présence se confirme jusqu'à une heure avant le créneau, et
-- dès que les DEUX joueurs sont réellement là, le plateau s'ouvre.
--
-- Ce qui ne bouge pas : l'horaire reste la référence pour les notifications,
-- la limite d'une heure pour rejoindre, et les forfaits. Le garde-fou de
-- présence reste entier — une confirmation vieille de plus de deux minutes ne
-- vaut pas présence, sinon on lancerait la partie contre un onglet endormi.
--
-- La borne d'une heure n'est pas décorative : `process_tournament_forfeits`
-- accorde la victoire par forfait à qui a confirmé sa présence. Sans borne, une
-- confirmation faite trois jours plus tôt vaudrait qualification contre un
-- joueur pourtant présent le jour dit.

CREATE OR REPLACE FUNCTION public.tournament_join_match(p_match_id uuid)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
declare
  v_uid uuid := auth.uid();
  v_match public.tournament_matches%rowtype;
  v_tournament public.tournaments%rowtype;
  v_result jsonb;
begin
  if v_uid is null then
    raise exception 'unauthenticated' using errcode = '42501';
  end if;

  select * into v_match from public.tournament_matches where id = p_match_id for update;

  if not found then raise exception 'match_not_found' using errcode = 'P0002'; end if;
  if v_uid not in (v_match.player1_id, v_match.player2_id) then
    raise exception 'not_a_participant' using errcode = '42501';
  end if;
  if (v_match.player1_id is null and not v_match.player1_slot_vacant)
     or (v_match.player2_id is null and not v_match.player2_slot_vacant) then
    raise exception 'opponent_slot_unresolved' using errcode = '23514';
  end if;
  if v_match.player1_slot_vacant and v_match.player2_slot_vacant then
    raise exception 'no_eligible_player' using errcode = '23514';
  end if;

  select * into v_tournament from public.tournaments where id = v_match.tournament_id for share;
  if not found then raise exception 'tournament_not_found' using errcode = 'P0002'; end if;

  if v_match.status in ('completed', 'walkover', 'cancelled') then
    return jsonb_build_object('success', false, 'status', v_match.status::text,
      'game_id', v_match.game_id, 'game_type', v_tournament.game_type, 'server_now', now());
  end if;

  if v_match.status not in ('pending', 'ready', 'in_progress') then
    raise exception 'match_not_ready' using errcode = '23514';
  end if;
  if v_tournament.status not in ('awaiting_start', 'in_progress') then
    raise exception 'tournament_not_in_progress' using errcode = '23514';
  end if;
  if v_match.scheduled_at is null then
    raise exception 'match_not_scheduled' using errcode = '23514';
  end if;
  -- Une heure d'avance, au lieu de cinq minutes : deux joueurs prets n'ont
  -- aucune raison d'attendre l'heure pile.
  if now() < v_match.scheduled_at - interval '1 hour' then
    raise exception 'join_window_not_open' using errcode = '23514';
  end if;
  if v_match.game_id is null and now() >= v_match.scheduled_at + interval '1 hour' then
    raise exception 'join_window_closed' using errcode = '23514';
  end if;

  -- La partie existe : on note quand meme le passage, puis on renvoie.
  if v_match.game_id is not null then
    if v_uid = v_match.player1_id then
      update public.tournament_matches set player1_last_seen_at = now(), updated_at = now()
       where id = p_match_id
         and (player1_last_seen_at is null or player1_last_seen_at <= now() - interval '15 seconds');
    else
      update public.tournament_matches set player2_last_seen_at = now(), updated_at = now()
       where id = p_match_id
         and (player2_last_seen_at is null or player2_last_seen_at <= now() - interval '15 seconds');
    end if;
    return jsonb_build_object('success', true, 'status', 'in_progress',
      'game_id', v_match.game_id, 'game_type', v_tournament.game_type, 'server_now', now(),
      'scheduled_at', v_match.scheduled_at, 'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  -- joined_at reste ecrit UNE fois : c'est lui qui ouvre le droit a la victoire
  -- par forfait. last_seen_at, lui, est rafraichi a chaque passage — mais pas
  -- plus d'une fois toutes les 15 secondes, pour ne pas rouvrir le robinet
  -- d'ecritures qu'on vient de fermer ailleurs.
  if v_uid = v_match.player1_id then
    update public.tournament_matches
       set player1_joined_at = coalesce(player1_joined_at, now()),
           player1_last_seen_at = case
             when player1_last_seen_at is null or player1_last_seen_at <= now() - interval '15 seconds'
               then now() else player1_last_seen_at end,
           ready_at = coalesce(ready_at, v_match.scheduled_at),
           status = case when status = 'pending' then 'ready'::public.tournament_match_status else status end,
           updated_at = now()
     where id = p_match_id;
  else
    update public.tournament_matches
       set player2_joined_at = coalesce(player2_joined_at, now()),
           player2_last_seen_at = case
             when player2_last_seen_at is null or player2_last_seen_at <= now() - interval '15 seconds'
               then now() else player2_last_seen_at end,
           ready_at = coalesce(ready_at, v_match.scheduled_at),
           status = case when status = 'pending' then 'ready'::public.tournament_match_status else status end,
           updated_at = now()
     where id = p_match_id;
  end if;

  if (v_uid = v_match.player1_id and v_match.player2_slot_vacant)
     or (v_uid = v_match.player2_id and v_match.player1_slot_vacant) then
    return jsonb_build_object('success', true, 'status', 'waiting_for_walkover_confirmation',
      'joined', true, 'game_id', null, 'game_type', v_tournament.game_type, 'server_now', now(),
      'scheduled_at', v_match.scheduled_at, 'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  v_result := public.create_tournament_game_if_ready(p_match_id);
  return v_result || jsonb_build_object('joined', true);
end;
$function$;

CREATE OR REPLACE FUNCTION public.create_tournament_game_if_ready(p_match_id uuid)
RETURNS jsonb
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
declare
  v_match public.tournament_matches%rowtype;
  v_tournament public.tournaments%rowtype;
  v_game_id uuid;
  v_window interval := make_interval(secs => public.tournament_presence_window_seconds());
  v_p1_here boolean;
  v_p2_here boolean;
begin
  select * into v_match from public.tournament_matches where id = p_match_id for update;
  if not found then raise exception 'match_not_found' using errcode = 'P0002'; end if;

  select * into v_tournament from public.tournaments where id = v_match.tournament_id for share;
  if not found then raise exception 'tournament_not_found' using errcode = 'P0002'; end if;

  if v_match.game_id is not null then
    return jsonb_build_object('success', true, 'status', v_match.status::text,
      'game_id', v_match.game_id, 'game_type', v_tournament.game_type, 'server_now', now(),
      'scheduled_at', v_match.scheduled_at, 'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  if v_match.status in ('completed', 'walkover', 'cancelled') then
    return jsonb_build_object('success', false, 'status', v_match.status::text,
      'game_id', null, 'game_type', v_tournament.game_type, 'server_now', now());
  end if;

  if v_match.player1_joined_at is null or v_match.player2_joined_at is null then
    return jsonb_build_object('success', true, 'status', 'waiting_for_opponent',
      'game_id', null, 'game_type', v_tournament.game_type, 'both_joined', false,
      'server_now', now(), 'scheduled_at', v_match.scheduled_at,
      'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  if v_tournament.status <> 'in_progress' then
    return jsonb_build_object('success', true, 'status', 'waiting_for_tournament_start',
      'game_id', null, 'game_type', v_tournament.game_type, 'both_joined', true,
      'server_now', now(), 'scheduled_at', v_match.scheduled_at,
      'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  -- L'heure officielle ne retient plus deux joueurs presents. Elle reste la
  -- reference pour les rappels et pour la limite d'une heure ci-dessous.

  if v_match.scheduled_at is not null
     and now() >= v_match.scheduled_at + interval '1 hour'
     and (v_match.player1_joined_at >= v_match.scheduled_at + interval '1 hour'
       or v_match.player2_joined_at >= v_match.scheduled_at + interval '1 hour') then
    return jsonb_build_object('success', false, 'status', 'join_window_closed',
      'game_id', null, 'game_type', v_tournament.game_type, 'server_now', now(),
      'scheduled_at', v_match.scheduled_at, 'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  -- LE GARDE-FOU. Un joueur qui a confirme sa presence il y a une demi-heure et
  -- dont l'onglet dort depuis n'est PAS present. Lancer la partie contre lui,
  -- c'est le condamner : il perdra par absence sans avoir jamais vu le plateau.
  -- Repli sur joined_at pour les clients pas encore mis a jour, mais seulement
  -- s'il est lui aussi recent : un ancien client qui vient de cliquer demarre
  -- normalement, un clic vieux d'une demi-heure non.
  v_p1_here := coalesce(v_match.player1_last_seen_at, v_match.player1_joined_at) >= now() - v_window;
  v_p2_here := coalesce(v_match.player2_last_seen_at, v_match.player2_joined_at) >= now() - v_window;

  if not (v_p1_here and v_p2_here) then
    return jsonb_build_object(
      'success', true,
      'status', 'waiting_for_opponent_return',
      'game_id', null,
      'game_type', v_tournament.game_type,
      'both_joined', true,
      'player1_present', v_p1_here,
      'player2_present', v_p2_here,
      'server_now', now(),
      'scheduled_at', v_match.scheduled_at,
      'join_deadline', v_match.scheduled_at + interval '1 hour');
  end if;

  perform set_config('app.trusted_game_write', '1', true);

  insert into public.games (
    game_type, player1_id, player2_id, bet_amount, is_sandbox, status, started_at,
    current_turn_player_id, turn_started_at, player1_bet_amount, player2_bet_amount,
    player1_is_ready, player2_is_ready, pregame_started_at, tournament_match_id,
    is_tournament, game_settings
  ) values (
    v_tournament.game_type::public.game_type, v_match.player1_id, v_match.player2_id,
    0, true, 'in_progress', now(), v_match.player1_id, now(), 0, 0, true, true, now(),
    v_match.id, true,
    jsonb_build_object('tournament_id', v_match.tournament_id,
      'tournament_match_id', v_match.id, 'wallet_settlement', false,
      'scheduled_at', v_match.scheduled_at)
  ) returning id into v_game_id;

  update public.tournament_matches
     set game_id = v_game_id, status = 'in_progress',
         ready_at = coalesce(ready_at, scheduled_at, now()),
         played_at = coalesce(played_at, now()), updated_at = now()
   where id = v_match.id;

  perform set_config('app.trusted_game_write', '', true);

  insert into public.notifications (user_id, type, title, message, data, status)
  select player_id, 'admin_announcement', '🎮 Votre match de tournoi est prêt',
         'Les deux joueurs sont présents. Ouvrez maintenant le plateau de '
           || coalesce(v_tournament.game_type, 'jeu') || '.',
         jsonb_build_object('kind', 'tournament_game_ready',
           'tournament_id', v_match.tournament_id, 'match_id', v_match.id,
           'game_id', v_game_id, 'game_type', v_tournament.game_type,
           'url', '/tournament-match/' || v_match.id::text),
         'unread'
    from unnest(array[v_match.player1_id, v_match.player2_id]) as player_id
   where player_id is not null;

  return jsonb_build_object('success', true, 'status', 'in_progress', 'game_id', v_game_id,
    'game_type', v_tournament.game_type, 'both_joined', true, 'server_now', now(),
    'scheduled_at', v_match.scheduled_at, 'join_deadline', v_match.scheduled_at + interval '1 hour');
exception
  when others then
    perform set_config('app.trusted_game_write', '', true);
    raise;
end;
$function$;

COMMENT ON FUNCTION public.create_tournament_game_if_ready(uuid) IS
  'Ouvre le plateau dès que les deux joueurs sont réellement présents, sans attendre l''heure officielle. Refuse de lancer contre un joueur dont la présence date de plus de deux minutes.';
