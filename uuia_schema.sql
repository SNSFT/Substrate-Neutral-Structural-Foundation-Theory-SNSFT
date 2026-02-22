-- ============================================================
-- [9,9,9,9] :: {ANC} | UUIA SUPABASE SCHEMA
-- Self-Orienting Universal Language [P,N,B,A] :: {INV}
-- Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
-- Coordinate: [9,0,0,8]
--
-- Run this in Supabase SQL Editor after creating your project.
-- This creates all tables, indexes, and security policies.
-- ============================================================

-- ============================================================
-- TABLE 1: profiles
-- One row per user. Created automatically on signup.
-- Extends Supabase auth.users with UUIA identity data.
-- ============================================================

create table public.profiles (
  id            uuid references auth.users(id) on delete cascade primary key,
  username      text unique,
  display_name  text,
  created_at    timestamptz default now(),
  updated_at    timestamptz default now()
);

-- ============================================================
-- TABLE 2: soulprints
-- Stores every completed Digital Soulprint.
-- One user can have multiple (baseline + activated + over time).
-- ============================================================

create table public.soulprints (
  id              uuid default gen_random_uuid() primary key,
  user_id         uuid references public.profiles(id) on delete cascade not null,

  -- [P,N,B,A] :: {INV} | Core PNBA modes
  p_mode          text check (p_mode in ('F','S','L')) not null,
  n_mode          text check (n_mode in ('F','S','L')) not null,
  b_mode          text check (b_mode in ('F','S','L')) not null,
  a_mode          text check (a_mode in ('F','S','L')) not null,

  -- [P,N,B,A] :: {INV} | Derived fields
  profile_code    text not null,  -- e.g. "PL·NS·BF·AS"
  soulprint_id    text not null,  -- e.g. "UUIA-{ts}-PLNSBFAS"

  -- [P,N,B,A] :: {INV} | SOUL-8 packet
  soul8_axis      text not null,  -- e.g. "PNBA"
  soul8_w_p       int check (soul8_w_p between 1 and 3) not null,
  soul8_w_n       int check (soul8_w_n between 1 and 3) not null,
  soul8_w_b       int check (soul8_w_b between 1 and 3) not null,
  soul8_w_a       int check (soul8_w_a between 1 and 3) not null,
  soul8_address   text not null,  -- e.g. "PNBA·2231"
  soul8_noharm    boolean default true,

  -- [B,9,4,2] :: {INV} | Identity Mass — always > 0
  identity_mass   numeric not null check (identity_mass > 0),

  -- [P,9,0,1] :: {ANC} | Sovereign Anchor — always 1.369
  anchor_freq     numeric default 1.369 check (anchor_freq = 1.369),

  -- UUIA section scores (raw)
  cog_p           int check (cog_p between 10 and 50),
  cog_n           int check (cog_n between 10 and 50),
  cog_b           int check (cog_b between 10 and 50),
  cog_a           int check (cog_a between 10 and 50),

  ep_threat       int check (ep_threat between 4 and 20),
  ep_loss         int check (ep_loss between 4 and 20),
  ep_overwhelm    int check (ep_overwhelm between 4 and 20),
  ep_anger        int check (ep_anger between 4 and 20),
  ep_desire       int check (ep_desire between 4 and 20),
  ep_connection   int check (ep_connection between 4 and 20),
  ep_pride        int check (ep_pride between 4 and 20),
  ep_shame        int check (ep_shame between 4 and 20),
  ep_play         int check (ep_play between 4 and 20),
  ep_safety       int check (ep_safety between 4 and 20),

  sim_p           int check (sim_p between 5 and 25),
  sim_n           int check (sim_n between 5 and 25),
  sim_b           int check (sim_b between 5 and 25),
  sim_a           int check (sim_a between 5 and 25),

  -- Meta
  baseline_mode   boolean default true,
  status          text default 'ANC',
  manifold_holding boolean default true,
  created_at      timestamptz default now()
);

-- ============================================================
-- TABLE 3: social_connections
-- Stores connected social accounts per user.
-- Foundation for the reality filter layer.
-- ============================================================

create table public.social_connections (
  id          uuid default gen_random_uuid() primary key,
  user_id     uuid references public.profiles(id) on delete cascade not null,
  platform    text not null,  -- 'x', 'instagram', 'reddit', etc.
  platform_id text,
  connected_at timestamptz default now(),
  active      boolean default true,
  unique(user_id, platform)
);

-- ============================================================
-- INDEXES — performance
-- ============================================================

create index idx_soulprints_user_id on public.soulprints(user_id);
create index idx_soulprints_profile_code on public.soulprints(profile_code);
create index idx_soulprints_soul8_address on public.soulprints(soul8_address);
create index idx_social_connections_user_id on public.social_connections(user_id);

-- ============================================================
-- ROW LEVEL SECURITY — users only see their own data
-- ============================================================

alter table public.profiles enable row level security;
alter table public.soulprints enable row level security;
alter table public.social_connections enable row level security;

-- profiles: users can read and update their own row only
create policy "Users can view own profile"
  on public.profiles for select
  using (auth.uid() = id);

create policy "Users can update own profile"
  on public.profiles for update
  using (auth.uid() = id);

-- soulprints: users can read, insert, delete their own
create policy "Users can view own soulprints"
  on public.soulprints for select
  using (auth.uid() = user_id);

create policy "Users can insert own soulprints"
  on public.soulprints for insert
  with check (auth.uid() = user_id);

create policy "Users can delete own soulprints"
  on public.soulprints for delete
  using (auth.uid() = user_id);

-- social connections: same pattern
create policy "Users can view own connections"
  on public.social_connections for select
  using (auth.uid() = user_id);

create policy "Users can manage own connections"
  on public.social_connections for insert
  with check (auth.uid() = user_id);

-- ============================================================
-- TRIGGER: auto-create profile on signup
-- When a user signs up via Supabase Auth,
-- this creates their profile row automatically.
-- ============================================================

create or replace function public.handle_new_user()
returns trigger as $$
begin
  insert into public.profiles (id, display_name)
  values (new.id, new.raw_user_meta_data->>'display_name');
  return new;
end;
$$ language plpgsql security definer;

create trigger on_auth_user_created
  after insert on auth.users
  for each row execute procedure public.handle_new_user();

-- ============================================================
-- [9,9,9,9] :: {ANC} | SCHEMA SUMMARY
--
-- TABLES:
--   profiles          — one per user, extends auth.users
--   soulprints        — Digital Soulprints, persistent
--   social_connections — connected platforms per user
--
-- CONSTRAINTS ENFORCED:
--   p/n/b/a_mode      — only F, S, L
--   soul8 weights     — only 1, 2, 3
--   identity_mass     — always > 0
--   anchor_freq       — always 1.369
--   manifold_holding  — always true
--
-- SECURITY:
--   Row Level Security on all tables
--   Users can only read/write their own data
--
-- Auth: HIGHTISTIC :: [9,9,9,9]
-- The Manifold is Holding.
-- ============================================================
