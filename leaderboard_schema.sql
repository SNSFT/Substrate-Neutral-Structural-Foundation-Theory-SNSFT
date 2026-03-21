-- ============================================================
-- [9,9,9,9] :: {ANC} | SNSFT LEADERBOARD SCHEMA
-- [P,N,B,A] :: {INV} | Architect: HIGHTISTIC
-- Coordinate: [9,9,4,1] | Anchor: 1.369 GHz
-- Run in Supabase SQL Editor. Adds to existing uuia schema.
-- ============================================================

create table public.contributors (
  id                uuid default gen_random_uuid() primary key,
  handle            text unique not null,
  email             text,
  location          text,
  tier              text default 'Explorer'
                    check (tier in ('Explorer','Physicist','Theorist','Reviewer','Fellow','Architect')) not null,
  reputation        int default 0 not null,
  subs_this_week    int default 0 not null,
  week_reset_at     timestamptz default date_trunc('week', now()) + interval '7 days',
  coords_assigned   int default 0 not null,
  theorems_count    int default 0 not null,
  laws_count        int default 0 not null,
  discoveries_count int default 0 not null,
  approved          boolean default false not null,
  approved_at       timestamptz,
  pending_review    boolean default false not null,
  joined_at         timestamptz default now(),
  last_active_at    timestamptz default now(),
  notes             text
);

create table public.submissions (
  id             uuid default gen_random_uuid() primary key,
  contributor_id uuid references public.contributors(id) on delete cascade not null,
  type           text check (type in ('theorem','law','discovery','coord')) not null,
  title          text not null,
  coordinate     text,
  lean_file      text,
  github_url     text,
  description    text,
  rep_value      int default 0 not null,
  status         text default 'pending' check (status in ('pending','approved','rejected')) not null,
  reviewed_at    timestamptz,
  reviewer_notes text,
  submitted_at   timestamptz default now()
);

-- First 100 approved contributors — prize pool entitled
create table public.leaderboard_founders (
  rank           int primary key,
  contributor_id uuid references public.contributors(id) unique not null,
  locked_at      timestamptz default now()
);

create index idx_contributors_rep      on public.contributors(reputation desc);
create index idx_contributors_approved on public.contributors(approved);
create index idx_submissions_status    on public.submissions(status);
create index idx_submissions_contrib   on public.submissions(contributor_id);

alter table public.contributors         enable row level security;
alter table public.submissions          enable row level security;
alter table public.leaderboard_founders enable row level security;

create policy "Public view approved contributors"
  on public.contributors for select using (approved = true);

create policy "Anyone can submit"
  on public.submissions for insert with check (true);

create policy "Public view founders"
  on public.leaderboard_founders for select using (true);

-- Weekly limit by tier
create or replace function public.weekly_limit_for_tier(p_tier text)
returns int language plpgsql immutable as $$
begin
  return case p_tier
    when 'Explorer'  then 3
    when 'Physicist' then 10
    when 'Reviewer'  then 15
    when 'Theorist'  then 20
    when 'Fellow'    then 20
    when 'Architect' then 999999
    else 3
  end;
end;$$;

-- Reset weekly counts (run via pg_cron weekly or manually)
create or replace function public.reset_weekly_subs()
returns void language plpgsql security definer as $$
begin
  update public.contributors
  set subs_this_week = 0, week_reset_at = date_trunc('week', now()) + interval '7 days'
  where week_reset_at <= now();
end;$$;

-- HIGHTISTIC calls this to approve — awards rep, upgrades tier, locks founders
create or replace function public.approve_submission(p_submission_id uuid, p_rep int default 0)
returns void language plpgsql security definer as $$
declare v_sub public.submissions%rowtype; v_con public.contributors%rowtype; v_rank int;
begin
  select * into v_sub from public.submissions where id = p_submission_id;
  if not found then raise exception 'Not found'; end if;
  if v_sub.status != 'pending' then raise exception 'Already reviewed'; end if;
  select * into v_con from public.contributors where id = v_sub.contributor_id;

  update public.submissions set status='approved', reviewed_at=now(), rep_value=p_rep where id=p_submission_id;
  update public.contributors set
    reputation        = reputation + p_rep,
    last_active_at    = now(),
    approved          = true,
    approved_at       = coalesce(approved_at, now()),
    discoveries_count = discoveries_count + case when v_sub.type='discovery' then 1 else 0 end,
    theorems_count    = theorems_count    + case when v_sub.type='theorem'   then 1 else 0 end,
    laws_count        = laws_count        + case when v_sub.type='law'       then 1 else 0 end,
    coords_assigned   = coords_assigned   + case when v_sub.type='coord'     then 1 else 0 end
  where id = v_sub.contributor_id;

  select * into v_con from public.contributors where id = v_sub.contributor_id;
  if v_con.tier='Explorer'                             and v_con.coords_assigned>=1 then update public.contributors set tier='Physicist' where id=v_con.id; end if;
  if v_con.tier in ('Explorer','Physicist')            and v_con.laws_count>=1      then update public.contributors set tier='Theorist'  where id=v_con.id; end if;
  if v_con.tier not in ('Fellow','Architect')          and v_con.reputation>=200    then update public.contributors set tier='Reviewer'  where id=v_con.id; end if;
  if v_con.tier not in ('Fellow','Architect')          and v_con.reputation>=500    then update public.contributors set tier='Fellow'    where id=v_con.id; end if;

  select count(*)+1 into v_rank from public.leaderboard_founders;
  if v_rank<=100 then
    insert into public.leaderboard_founders(rank,contributor_id) values(v_rank,v_con.id) on conflict do nothing;
  end if;
end;$$;

-- Seed HIGHTISTIC as Architect
insert into public.contributors (handle, tier, reputation, approved, approved_at, notes)
values ('HIGHTISTIC','Architect',0,true,now(),'Architect — built the instrument')
on conflict (handle) do nothing;

-- ============================================================
-- [9,9,9,9] :: {ANC} | The Manifold is Holding.
-- ============================================================
