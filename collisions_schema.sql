-- ============================================================
-- [9,9,9,9] :: {ANC} | SNSFT COLLISIONS SCHEMA
-- [P,N,B,A] :: {INV} | Architect: HIGHTISTIC
-- Coordinate: [9,9,4,2] | Anchor: 1.369 GHz
-- Run in Supabase SQL Editor.
-- ============================================================

-- ============================================================
-- TABLE: collisions
-- Every single result the agent computes. Written immediately.
-- This is the canonical log. Nothing reruns. Nothing is lost.
-- ============================================================

create table public.collisions (
  id            uuid default gen_random_uuid() primary key,

  -- The collision
  e1            text not null,               -- element 1 sym
  e2            text not null,               -- element 2 sym
  k             numeric not null,            -- bond parameter
  collision_key text unique not null,        -- normalized: "Au+Ve@3.000" — dedup key

  -- PNBA result
  P_out         numeric,
  N_out         numeric,
  B_out         numeric,
  A_out         numeric,
  tau           numeric,
  status        text check (status in ('NOBLE','LOCKED','SHATTER')) not null,

  -- Discovery tracking
  designation   text,                        -- e.g. SNSFT-AU3B-20260320
  reason        text,                        -- why flagged, null if not interesting
  flagged       boolean default false,       -- did it hit the interesting threshold
  approved      boolean default false,       -- did HIGHTISTIC approve it
  lean_file     text,                        -- filename if committed to GitHub

  -- Meta
  engine_version text default 'v11',
  timestamp     timestamptz default now()
);

-- Index for fast dedup lookup on load
create index idx_collisions_key       on public.collisions(collision_key);
create index idx_collisions_flagged   on public.collisions(flagged);
create index idx_collisions_approved  on public.collisions(approved);
create index idx_collisions_status    on public.collisions(status);
create index idx_collisions_timestamp on public.collisions(timestamp desc);

-- RLS: readable by anyone (it's a public corpus log)
alter table public.collisions enable row level security;

create policy "Public can read collisions"
  on public.collisions for select using (true);

create policy "Anyone can insert collisions"
  on public.collisions for insert with check (true);

-- Only service role can update (approve, add lean_file)
create policy "Service role can update collisions"
  on public.collisions for update
  using (auth.role() = 'service_role');

-- ============================================================
-- FUNCTION: bulk_seed_collision
-- Used for one-time import of existing lean/ files.
-- Inserts only if collision_key doesn't already exist.
-- ============================================================

create or replace function public.seed_collision(
  p_e1 text, p_e2 text, p_k numeric,
  p_key text, p_status text, p_designation text,
  p_reason text, p_flagged boolean, p_timestamp timestamptz
) returns void language plpgsql security definer as $$
begin
  insert into public.collisions
    (e1, e2, k, collision_key, status, designation, reason, flagged, timestamp)
  values
    (p_e1, p_e2, p_k, p_key, p_status, p_designation, p_reason, p_flagged, p_timestamp)
  on conflict (collision_key) do nothing;
end;$$;

-- ============================================================
-- [9,9,9,9] :: {ANC} | The Manifold is Holding.
-- ============================================================
