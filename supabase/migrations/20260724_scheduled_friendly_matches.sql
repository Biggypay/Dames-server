-- Scheduled friendly matches: two friends agree on a future time to play; the
-- system reminds both N minutes before. All writes go through SECURITY DEFINER
-- RPCs; clients only read their own rows (RLS) and receive realtime updates.
create table if not exists public.scheduled_matches (
  id uuid primary key default gen_random_uuid(),
  proposer_id uuid not null references public.profiles(id) on delete cascade,
  opponent_id uuid not null references public.profiles(id) on delete cascade,
  game_type public.game_type not null,
  scheduled_at timestamptz not null,
  reminder_minutes integer not null default 10,
  status text not null default 'pending' check (status in ('pending','accepted','declined','cancelled')),
  reminder_sent boolean not null default false,
  created_at timestamptz not null default now(),
  updated_at timestamptz not null default now(),
  constraint scheduled_matches_distinct_players check (proposer_id <> opponent_id),
  constraint scheduled_matches_reminder_bounds check (reminder_minutes between 1 and 720)
);

create index if not exists idx_scheduled_matches_opponent on public.scheduled_matches(opponent_id, status);
create index if not exists idx_scheduled_matches_proposer on public.scheduled_matches(proposer_id, status);
create index if not exists idx_scheduled_matches_due on public.scheduled_matches(scheduled_at) where status='accepted' and reminder_sent=false;

alter table public.scheduled_matches enable row level security;
alter table public.scheduled_matches replica identity full;

drop policy if exists "Participants view scheduled matches" on public.scheduled_matches;
create policy "Participants view scheduled matches" on public.scheduled_matches
  for select to authenticated
  using (auth.uid() = proposer_id or auth.uid() = opponent_id);

do $$ begin
  if not exists (select 1 from pg_publication_tables where pubname='supabase_realtime' and schemaname='public' and tablename='scheduled_matches') then
    alter publication supabase_realtime add table public.scheduled_matches;
  end if;
end $$;

create or replace function public.are_users_friends(a uuid, b uuid)
returns boolean language sql stable security definer set search_path=public, pg_temp as $$
  select exists (
    select 1 from public.friends f
    where f.status='accepted'
      and ((f.user_id=a and f.friend_id=b) or (f.user_id=b and f.friend_id=a))
  );
$$;
revoke all on function public.are_users_friends(uuid,uuid) from public, anon;
grant execute on function public.are_users_friends(uuid,uuid) to authenticated, service_role;

create or replace function public.propose_scheduled_match(
  p_opponent_id uuid, p_game_type public.game_type,
  p_scheduled_at timestamptz, p_reminder_minutes integer default 10
) returns jsonb language plpgsql security definer set search_path=public, pg_temp as $$
declare v_uid uuid := auth.uid(); v_id uuid; v_name text;
begin
  if v_uid is null then raise exception 'authentication_required'; end if;
  if p_opponent_id is null or p_opponent_id = v_uid then raise exception 'invalid_opponent'; end if;
  if not public.are_users_friends(v_uid, p_opponent_id) then raise exception 'friends_only'; end if;
  if p_scheduled_at <= now() + interval '5 minutes' then raise exception 'time_too_soon'; end if;
  if p_scheduled_at > now() + interval '30 days' then raise exception 'time_too_far'; end if;
  if coalesce(p_reminder_minutes,10) not in (5,10,15,30,60) then raise exception 'invalid_reminder'; end if;

  insert into public.scheduled_matches (proposer_id, opponent_id, game_type, scheduled_at, reminder_minutes)
  values (v_uid, p_opponent_id, p_game_type, p_scheduled_at, coalesce(p_reminder_minutes,10))
  returning id into v_id;

  select username into v_name from public.profiles where id=v_uid;
  insert into public.notifications (user_id, type, title, message, data, status)
  values (p_opponent_id, 'admin_announcement', '📅 Proposition de match',
    coalesce(v_name,'Un ami') || ' vous propose un match le ' ||
      to_char(p_scheduled_at at time zone 'America/Port-au-Prince','DD/MM à HH24:MI') || '.',
    jsonb_build_object('kind','scheduled_match_proposal','scheduled_match_id',v_id,'game_type',p_game_type,'scheduled_at',p_scheduled_at,'from',v_uid),
    'unread');

  return jsonb_build_object('ok',true,'id',v_id);
end; $$;
revoke all on function public.propose_scheduled_match(uuid,public.game_type,timestamptz,integer) from public, anon;
grant execute on function public.propose_scheduled_match(uuid,public.game_type,timestamptz,integer) to authenticated;

create or replace function public.respond_scheduled_match(p_id uuid, p_accept boolean)
returns jsonb language plpgsql security definer set search_path=public, pg_temp as $$
declare v_uid uuid := auth.uid(); m public.scheduled_matches%rowtype; v_name text;
begin
  if v_uid is null then raise exception 'authentication_required'; end if;
  select * into m from public.scheduled_matches where id=p_id for update;
  if not found then raise exception 'not_found'; end if;
  if m.opponent_id <> v_uid then raise exception 'not_opponent'; end if;
  if m.status <> 'pending' then return jsonb_build_object('ok',true,'status',m.status); end if;

  update public.scheduled_matches set status = case when p_accept then 'accepted' else 'declined' end, updated_at=now() where id=p_id;

  select username into v_name from public.profiles where id=v_uid;
  insert into public.notifications (user_id, type, title, message, data, status)
  values (m.proposer_id, 'admin_announcement',
    case when p_accept then '✅ Match accepté' else '❌ Match refusé' end,
    coalesce(v_name,'Votre ami') || case when p_accept
      then ' a accepté le match du ' || to_char(m.scheduled_at at time zone 'America/Port-au-Prince','DD/MM à HH24:MI') || '.'
      else ' a refusé votre proposition de match.' end,
    jsonb_build_object('kind','scheduled_match_response','scheduled_match_id',m.id,'accepted',p_accept),
    'unread');

  return jsonb_build_object('ok',true,'status', case when p_accept then 'accepted' else 'declined' end);
end; $$;
revoke all on function public.respond_scheduled_match(uuid,boolean) from public, anon;
grant execute on function public.respond_scheduled_match(uuid,boolean) to authenticated;

create or replace function public.cancel_scheduled_match(p_id uuid)
returns jsonb language plpgsql security definer set search_path=public, pg_temp as $$
declare v_uid uuid := auth.uid(); m public.scheduled_matches%rowtype;
begin
  if v_uid is null then raise exception 'authentication_required'; end if;
  select * into m from public.scheduled_matches where id=p_id for update;
  if not found then raise exception 'not_found'; end if;
  if v_uid not in (m.proposer_id, m.opponent_id) then raise exception 'not_participant'; end if;
  if m.status in ('declined','cancelled') then return jsonb_build_object('ok',true,'status',m.status); end if;
  update public.scheduled_matches set status='cancelled', updated_at=now() where id=p_id;
  return jsonb_build_object('ok',true,'status','cancelled');
end; $$;
revoke all on function public.cancel_scheduled_match(uuid) from public, anon;
grant execute on function public.cancel_scheduled_match(uuid) to authenticated;

create or replace function public.process_scheduled_match_reminders()
returns void language plpgsql security definer set search_path=public, pg_temp as $$
declare r record;
begin
  for r in
    select * from public.scheduled_matches
    where status='accepted' and reminder_sent=false and scheduled_at > now()
      and scheduled_at <= now() + make_interval(mins => reminder_minutes)
    for update skip locked
  loop
    update public.scheduled_matches set reminder_sent=true, updated_at=now() where id=r.id;
    insert into public.notifications (user_id, type, title, message, data, status)
    select uid, 'admin_announcement', '⏰ Votre match approche',
      'Votre match planifié commence à ' || to_char(r.scheduled_at at time zone 'America/Port-au-Prince','HH24:MI') || '.',
      jsonb_build_object('kind','scheduled_match_reminder','scheduled_match_id',r.id,'game_type',r.game_type,'scheduled_at',r.scheduled_at),
      'unread'
    from unnest(array[r.proposer_id, r.opponent_id]) as uid;
  end loop;

  update public.scheduled_matches set status='cancelled', updated_at=now()
   where status='pending' and scheduled_at < now();
end; $$;
revoke all on function public.process_scheduled_match_reminders() from public, anon, authenticated;
grant execute on function public.process_scheduled_match_reminders() to service_role;

do $$ begin
  perform cron.unschedule('mindspille-scheduled-match-reminders');
exception when others then null; end $$;
select cron.schedule('mindspille-scheduled-match-reminders','* * * * *','select public.process_scheduled_match_reminders();');
