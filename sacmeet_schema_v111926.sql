-- ============================================================
-- SacMeet — Kernel schema (Supabase / Postgres)
-- SNSFT Foundation · HIGHTISTIC (Russell Vernon Trent III) · Kenai, Alaska
--
-- The kernel holds authority (P): who is in a space and what they may do.
-- Every rule below is enforced by the database itself (row-level security),
-- so no page, plugin or API client can grant itself a role it was not given.
--
-- Four services, one per axis:
--   P  spaces, members, roles      structure and authority
--   N  messages                    the record that persists
--   B  voice rooms                 the live link (signaling runs on Realtime)
--   A  moderation                  roles, kick, delete, rate limits
--
-- Run once in the Supabase SQL editor of the project.
-- ============================================================

create extension if not exists pgcrypto;

-- ── profiles ────────────────────────────────────────────────
create table if not exists public.profiles (
  id         uuid primary key references auth.users on delete cascade,
  handle     text unique check (char_length(handle) between 2 and 32),
  created_at timestamptz not null default now()
);

-- ── spaces (P) ──────────────────────────────────────────────
create table if not exists public.spaces (
  id          uuid primary key default gen_random_uuid(),
  name        text not null check (char_length(name) between 1 and 64),
  owner       uuid not null default auth.uid() references auth.users on delete cascade,
  invite_code text not null unique default encode(gen_random_bytes(6), 'hex'),
  created_at  timestamptz not null default now()
);

create table if not exists public.members (
  space_id  uuid not null references public.spaces on delete cascade,
  user_id   uuid not null references auth.users on delete cascade,
  role      text not null default 'member' check (role in ('owner','mod','member')),
  joined_at timestamptz not null default now(),
  primary key (space_id, user_id)
);

create table if not exists public.channels (
  id         uuid primary key default gen_random_uuid(),
  space_id   uuid not null references public.spaces on delete cascade,
  name       text not null check (char_length(name) between 1 and 48),
  kind       text not null default 'text' check (kind in ('text','voice')),
  created_at timestamptz not null default now()
);

-- ── messages (N) ────────────────────────────────────────────
create table if not exists public.messages (
  id         bigint generated always as identity primary key,
  channel_id uuid not null references public.channels on delete cascade,
  author     uuid not null default auth.uid() references auth.users on delete cascade,
  body       text not null check (char_length(body) between 1 and 4000),
  created_at timestamptz not null default now()
);
create index if not exists messages_channel_time on public.messages (channel_id, created_at);
create index if not exists messages_author_time  on public.messages (author, created_at);

-- ── kernel reads (security definer, so policies never recurse) ──
create or replace function public.role_in(sp uuid)
returns text language sql stable security definer set search_path = public as $$
  select role from public.members where space_id = sp and user_id = auth.uid()
$$;

create or replace function public.is_member(sp uuid)
returns boolean language sql stable security definer set search_path = public as $$
  select exists (select 1 from public.members where space_id = sp and user_id = auth.uid())
$$;

create or replace function public.space_of(ch uuid)
returns uuid language sql stable security definer set search_path = public as $$
  select space_id from public.channels where id = ch
$$;

-- ── a new space seats its owner and opens two channels ──────
create or replace function public.on_space_created()
returns trigger language plpgsql security definer set search_path = public as $$
begin
  insert into public.members (space_id, user_id, role) values (new.id, new.owner, 'owner');
  insert into public.channels (space_id, name, kind) values (new.id, 'general', 'text');
  insert into public.channels (space_id, name, kind) values (new.id, 'lounge', 'voice');
  return new;
end $$;

drop trigger if exists space_created on public.spaces;
create trigger space_created after insert on public.spaces
  for each row execute function public.on_space_created();

-- ── creating a space goes through the kernel ────────────────
create or replace function public.create_space(space_name text)
returns uuid language plpgsql security definer set search_path = public as $$
declare sp uuid;
begin
  if auth.uid() is null then raise exception 'sign in first'; end if;
  insert into public.spaces (name, owner) values (space_name, auth.uid()) returning id into sp;
  return sp;
end $$;

-- ── joining goes through the kernel, by invite code only ────
create or replace function public.join_space(code text)
returns uuid language plpgsql security definer set search_path = public as $$
declare sp uuid;
begin
  if auth.uid() is null then raise exception 'sign in first'; end if;
  select id into sp from public.spaces where invite_code = code;
  if sp is null then raise exception 'no space with that invite code'; end if;
  insert into public.members (space_id, user_id, role) values (sp, auth.uid(), 'member')
    on conflict do nothing;
  return sp;
end $$;

-- ── roles change only downward from the owner, never to owner ──
create or replace function public.guard_role_change()
returns trigger language plpgsql security definer set search_path = public as $$
begin
  if new.role = 'owner' and old.role <> 'owner' then
    raise exception 'ownership is not assignable';
  end if;
  if old.role = 'owner' and new.role <> 'owner' then
    raise exception 'the owner role stays with the owner';
  end if;
  if new.space_id <> old.space_id or new.user_id <> old.user_id then
    raise exception 'membership identity is fixed';
  end if;
  return new;
end $$;

drop trigger if exists role_guard on public.members;
create trigger role_guard before update on public.members
  for each row execute function public.guard_role_change();

-- ── suppress_collapse: a sender over the limit is clamped ───
-- More than 8 messages in 10 seconds from one author is refused;
-- the space and everyone else in it keep running.
create or replace function public.rate_limit_messages()
returns trigger language plpgsql security definer set search_path = public as $$
begin
  if (select count(*) from public.messages
       where author = new.author and created_at > now() - interval '10 seconds') >= 8 then
    raise exception 'rate_limited';
  end if;
  return new;
end $$;

drop trigger if exists message_rate on public.messages;
create trigger message_rate before insert on public.messages
  for each row execute function public.rate_limit_messages();

-- ── row-level security ──────────────────────────────────────
alter table public.profiles enable row level security;
alter table public.spaces   enable row level security;
alter table public.members  enable row level security;
alter table public.channels enable row level security;
alter table public.messages enable row level security;

-- profiles: anyone signed in can read handles; each person writes their own
drop policy if exists profiles_read on public.profiles;
create policy profiles_read on public.profiles for select to authenticated using (true);
drop policy if exists profiles_write on public.profiles;
create policy profiles_write on public.profiles for insert to authenticated with check (id = auth.uid());
drop policy if exists profiles_update on public.profiles;
create policy profiles_update on public.profiles for update to authenticated using (id = auth.uid());

-- spaces: members read; anyone signed in creates their own; owner edits or deletes
drop policy if exists spaces_read on public.spaces;
create policy spaces_read on public.spaces for select to authenticated using (public.is_member(id));
drop policy if exists spaces_create on public.spaces;
create policy spaces_create on public.spaces for insert to authenticated with check (owner = auth.uid());
drop policy if exists spaces_owner_update on public.spaces;
create policy spaces_owner_update on public.spaces for update to authenticated using (public.role_in(id) = 'owner');
drop policy if exists spaces_owner_delete on public.spaces;
create policy spaces_owner_delete on public.spaces for delete to authenticated using (public.role_in(id) = 'owner');

-- members: members see the roster; the owner sets roles; you may leave,
-- a mod or owner may remove a member, and nobody removes the owner
drop policy if exists members_read on public.members;
create policy members_read on public.members for select to authenticated using (public.is_member(space_id));
drop policy if exists members_role on public.members;
create policy members_role on public.members for update to authenticated
  using (public.role_in(space_id) = 'owner');
drop policy if exists members_remove on public.members;
create policy members_remove on public.members for delete to authenticated
  using (role <> 'owner' and (user_id = auth.uid() or public.role_in(space_id) in ('owner','mod')));

-- channels: members read; mods and the owner manage
drop policy if exists channels_read on public.channels;
create policy channels_read on public.channels for select to authenticated using (public.is_member(space_id));
drop policy if exists channels_manage on public.channels;
create policy channels_manage on public.channels for all to authenticated
  using (public.role_in(space_id) in ('owner','mod'))
  with check (public.role_in(space_id) in ('owner','mod'));

-- messages: members read and write as themselves; authors and mods delete
drop policy if exists messages_read on public.messages;
create policy messages_read on public.messages for select to authenticated
  using (public.is_member(public.space_of(channel_id)));
drop policy if exists messages_write on public.messages;
create policy messages_write on public.messages for insert to authenticated
  with check (author = auth.uid() and public.is_member(public.space_of(channel_id)));
drop policy if exists messages_delete on public.messages;
create policy messages_delete on public.messages for delete to authenticated
  using (author = auth.uid() or public.role_in(public.space_of(channel_id)) in ('owner','mod'));

-- ── live updates for the record ─────────────────────────────
do $$ begin
  alter publication supabase_realtime add table public.messages;
exception when duplicate_object then null; end $$;
do $$ begin
  alter publication supabase_realtime add table public.members;
exception when duplicate_object then null; end $$;
do $$ begin
  alter publication supabase_realtime add table public.channels;
exception when duplicate_object then null; end $$;
