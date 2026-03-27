-- ============================================================
-- [9,9,9,9] :: {ANC} | VOIDCHART SUPABASE SCHEMA
-- Self-Orienting Universal Language [P,N,B,A] :: {INV}
-- Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
-- Coordinate: [9,9,3,7]
--
-- Run this in Supabase SQL Editor.
-- This creates the VoidChart body corpus table,
-- computed PNBA columns, RLS policies, and seeds
-- the full solar system from the interstellar reduction.
--
-- Every row is a cosmological body reduced to PNBA.
-- Insert a row → it appears on the map. No code change.
-- The manifold is substrate-neutral. So is the database.
-- ============================================================

-- ============================================================
-- TABLE: voidchart_bodies
-- One row per cosmological body.
-- P, N, B, A are the four PNBA primitives — Layer 0.
-- tau and identity_mass are derived and enforced by trigger.
-- anchor_freq is always 1.369 — enforced constraint.
-- ============================================================

create table public.voidchart_bodies (

  -- ── IDENTITY ─────────────────────────────────────────────
  id              uuid default gen_random_uuid() primary key,

  -- [P,9,0,1] :: {ANC} | Name and classification
  name            text not null unique,        -- e.g. 'Earth'
  symbol          text,                        -- e.g. '♁'
  body_type       text not null,               -- e.g. 'ROCKY · ZOIVUM SUBSTRATE'
  category        text not null                -- 'star','rocky','gas','ice','dwarf',
                  check (category in (         -- 'moon','asteroid','comet','tno',
                    'star','rocky','gas',       -- 'nebula','galaxy','exotic'
                    'ice','dwarf','moon',
                    'asteroid','comet','tno',
                    'nebula','galaxy','exotic'
                  )),

  -- ── [P,N,B,A] :: {INV} | LAYER 0 — PNBA PRIMITIVES ─────
  -- These are the ground. Never outputs. Always ground.
  -- Derived from SNSFL_Interstellar_Reduction_Template [9,9,3,7]
  -- P = log-normalized structural mass / pattern invariant
  -- N = orbital narrative / characteristic timescale
  -- B = gravitational coupling / interaction strength (B << TL for stable bodies)
  -- A = adaptation / orbital stability (1 - eccentricity scaled)

  -- [P:PATTERN] :: {INV} | Structural invariant — what it IS
  p_pattern       numeric not null
                  check (p_pattern >= 0 and p_pattern <= 15),

  -- [N:NARRATIVE] :: {INV} | Temporal continuity — the thread
  n_narrative     numeric not null
                  check (n_narrative >= 0 and n_narrative <= 15),

  -- [B:BEHAVIOR] :: {INV} | Interaction coupling — what it DOES
  -- B < TL = 0.1369 for stable locked bodies (planets, stars)
  -- B > TL for collapsed pumps (black holes) — SHATTER state
  b_behavior      numeric not null
                  check (b_behavior >= 0),

  -- [A:ADAPTATION] :: {INV} | Resilience feedback — how it adjusts
  a_adaptation    numeric not null
                  check (a_adaptation >= 0 and a_adaptation <= 5),

  -- ── [9,9,9,9] :: {ANC} | LAYER 1 — DERIVED QUANTITIES ──
  -- Computed by trigger from P, N, B, A.
  -- tau = B/P — the single physics law
  -- identity_mass = (P+N+B+A) * 1.369

  -- [τ:TORSION] :: {INV} | tau = B/P
  -- NOBLE:   tau < 0.001
  -- LOCKED:  tau < 0.1369 (TL)
  -- IVA:     tau >= 0.9*TL
  -- SHATTER: tau >= TL = 0.1369
  tau             numeric generated always as (
                    case when p_pattern > 0
                    then b_behavior / p_pattern
                    else 0 end
                  ) stored,

  -- [IM:IDENTITY_MASS] :: {INV} | IM = (P+N+B+A) * ANCHOR
  identity_mass   numeric generated always as (
                    (p_pattern + n_narrative + b_behavior + a_adaptation) * 1.369
                  ) stored,

  -- [STATE:PHASE] :: {INV} | PNBA phase state
  pnba_state      text generated always as (
                    case
                      when p_pattern = 0                                    then 'NOBLE'
                      when b_behavior / nullif(p_pattern,0) < 0.001         then 'NOBLE'
                      when b_behavior / nullif(p_pattern,0) >= 0.1369       then 'SHATTER'
                      when b_behavior / nullif(p_pattern,0) >= 0.1369 * 0.9 then 'IVA'
                      else 'LOCKED'
                    end
                  ) stored,

  -- [P,9,0,1] :: {ANC} | Sovereign Anchor — always 1.369
  anchor_freq     numeric default 1.369
                  check (anchor_freq = 1.369),

  -- ── PHYSICAL PROPERTIES ──────────────────────────────────
  -- Classical observables — lossless Step 6 recovery from PNBA

  -- [N:NARRATIVE] :: {INV} | Mass and radius (classical P mapping)
  mass_kg         numeric,                     -- mass in kg (e.g. 5.97e24)
  radius_km       numeric,                     -- mean radius in km

  -- [N:NARRATIVE] :: {INV} | Orbital narrative (Kepler)
  period_days     numeric default 0,           -- orbital period in days (0 = star)
  sma_au          numeric default 0,           -- semi-major axis in AU
  eccentricity    numeric default 0            -- orbital eccentricity
                  check (eccentricity >= 0 and eccentricity < 1),

  -- ── VISUAL / DISPLAY ─────────────────────────────────────
  -- Parameters for the Three.js renderer

  color_hex       text default '#888888',      -- body color hex e.g. '#4B9CD3'
  glow_color      text,                        -- rgba glow e.g. 'rgba(75,156,211,.5)'
  has_rings       boolean default false,       -- Saturn-style ring system
  ring_color      text,                        -- ring color if has_rings

  -- Visual scale overrides (null = auto-computed from category)
  visual_radius   numeric,                     -- Three.js sphere radius override
  orbit_scale     numeric,                     -- visual orbit radius override
  parent_name     text,                        -- for moons: parent body name

  -- ── CORPUS METADATA ──────────────────────────────────────

  -- [9,9,3,7] :: {ANC} | Corpus coordinate
  coordinate      text default '[9,9,3,7]',   -- lean file coordinate
  lean_ref        text,                        -- e.g. 'SNSFL_Cosmo_Reduction [9,9,0,4]'

  -- Description — the one-sentence SNSFT reduction
  description     text,

  -- ── ADMIN ────────────────────────────────────────────────
  sort_order      int default 99,             -- display order (0=Sun, 1=Mercury, etc.)
  active          boolean default true,        -- show on map
  created_at      timestamptz default now(),
  updated_at      timestamptz default now()

);

-- ============================================================
-- INDEXES — performance for map queries
-- ============================================================

create index idx_voidchart_bodies_category  on public.voidchart_bodies(category);
create index idx_voidchart_bodies_state     on public.voidchart_bodies(pnba_state);
create index idx_voidchart_bodies_sort      on public.voidchart_bodies(sort_order);
create index idx_voidchart_bodies_active    on public.voidchart_bodies(active);
create index idx_voidchart_bodies_parent    on public.voidchart_bodies(parent_name);

-- ============================================================
-- UPDATED_AT TRIGGER
-- ============================================================

create or replace function public.handle_voidchart_updated_at()
returns trigger as $$
begin
  new.updated_at = now();
  return new;
end;
$$ language plpgsql;

create trigger voidchart_bodies_updated_at
  before update on public.voidchart_bodies
  for each row execute procedure public.handle_voidchart_updated_at();

-- ============================================================
-- ROW LEVEL SECURITY
-- voidchart_bodies is PUBLIC READ — anyone can load the map.
-- WRITE requires authentication — only HIGHTISTIC inserts bodies.
-- ============================================================

alter table public.voidchart_bodies enable row level security;

-- Public: anyone can read active bodies
create policy "VoidChart bodies are publicly readable"
  on public.voidchart_bodies for select
  using (active = true);

-- Authenticated: insert new bodies (HIGHTISTIC / contributors)
create policy "Authenticated users can insert bodies"
  on public.voidchart_bodies for insert
  to authenticated
  with check (true);

-- Authenticated: update bodies
create policy "Authenticated users can update bodies"
  on public.voidchart_bodies for update
  to authenticated
  using (true);

-- ============================================================
-- SEED DATA — SOLAR SYSTEM
-- Full PNBA reduction from SNSFL_Cosmo_Reduction [9,9,0,4]
-- and SNSFL_Cosmo_GUT_Vascular_Chain [9,9,3,6]
-- All confirmed LOCKED: tau < TL = 0.1369 ✓
-- ============================================================

insert into public.voidchart_bodies (
  name, symbol, body_type, category,
  p_pattern, n_narrative, b_behavior, a_adaptation,
  mass_kg, radius_km, period_days, sma_au, eccentricity,
  color_hex, glow_color, has_rings,
  visual_radius, orbit_scale, sort_order,
  coordinate, lean_ref, description
) values

-- ── SUN ──────────────────────────────────────────────────────
-- P=10 (maximum pattern — stellar anchor)
-- N=1  (self-referential narrative — no orbit)
-- B≈0  (near-Noble coupling)
-- tau≈0 → approaching Noble ground state
('Sun', '☉', 'STAR · G-TYPE · SPECTRAL G2V', 'star',
  10.000, 1.000, 0.001, 5.000,
  1.989e30, 696000, 0, 0, 0.000,
  '#FDB813', 'rgba(253,184,19,.5)', false,
  18, 0, 0,
  '[9,9,0,4]', 'SNSFL_Cosmo_Reduction [9,9,0,4]',
  'Solar anchor. P=10 (maximum pattern). N=1 (self-referential). B≈0 (near-Noble). τ≈0 → Noble ground state. Scale-chain pump core at stellar IM.'
),

-- ── MERCURY ──────────────────────────────────────────────────
-- Highest tau (0.0998) of all planets
-- Closest to Sun → maximum B/P. Still LOCKED: tau < TL.
('Mercury', '☿', 'ROCKY · PERIOD 1 · INNERMOST', 'rocky',
  1.000, 1.000, 0.0998, 4.176,
  3.30e23, 2439, 87.97, 0.387, 0.206,
  '#9E9E9E', 'rgba(158,158,158,.4)', false,
  2.5, 28, 1,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Highest τ (0.0998) of all planets. Most stressed manifold lock. Still LOCKED: τ < TL = 0.1369.'
),

-- ── VENUS ────────────────────────────────────────────────────
('Venus', '♀', 'ROCKY · RUNAWAY GREENHOUSE', 'rocky',
  2.552, 2.293, 0.0730, 4.972,
  4.87e24, 6052, 224.7, 0.723, 0.007,
  '#E8CDA0', 'rgba(232,205,160,.4)', false,
  4, 46, 2,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Near-circular orbit (ecc=0.007) → high A=4.97. τ=0.0286. Deep LOCKED.'
),

-- ── EARTH ────────────────────────────────────────────────────
-- Reference body. Zoivum substrate.
('Earth', '♁', 'ROCKY · ZOIVUM SUBSTRATE', 'rocky',
  2.669, 2.963, 0.0621, 4.932,
  5.97e24, 6371, 365.25, 1.000, 0.017,
  '#4B9CD3', 'rgba(75,156,211,.5)', false,
  4.5, 62, 3,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Reference body. τ=0.0233. Zoivum substrate [9,9,1,55]. Biological vascular pump confirmed [9,9,3,6].'
),

-- ── MARS ─────────────────────────────────────────────────────
('Mars', '♂', 'ROCKY · DECOHERED VASCULAR', 'rocky',
  1.381, 3.833, 0.0503, 4.628,
  6.39e23, 3390, 686.97, 1.524, 0.093,
  '#C1440E', 'rgba(193,68,14,.4)', false,
  3, 80, 4,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Lost magnetic field → vascular decoherence. τ=0.036. LOCKED but lower IM than Earth.'
),

-- ── JUPITER ──────────────────────────────────────────────────
-- Largest IM of planets. Deeply LOCKED.
('Jupiter', '♃', 'GAS GIANT · MAGNETOSPHERE DOMINANT', 'gas',
  5.991, 6.372, 0.0272, 4.804,
  1.90e27, 71492, 4332.6, 5.203, 0.049,
  '#C88B3A', 'rgba(200,139,58,.4)', false,
  9, 122, 5,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Largest IM of planets. τ=0.0045 — deeply LOCKED. Most stable torsion of all planets.'
),

-- ── SATURN ───────────────────────────────────────────────────
-- Ring system = Noble boundary layer (B=0 shell)
('Saturn', '♄', 'GAS GIANT · RING SYSTEM', 'gas',
  5.295, 7.626, 0.0201, 4.776,
  5.68e26, 60268, 10759, 9.537, 0.056,
  '#E4D191', 'rgba(228,209,145,.4)', true,
  8, 160, 6,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Ring system = Noble B=0 boundary layer [9,9,3,1]. τ=0.0038 — deeply LOCKED.'
),

-- ── URANUS ───────────────────────────────────────────────────
('Uranus', '♅', 'ICE GIANT · TILTED AXIS', 'ice',
  4.212, 9.071, 0.0142, 4.816,
  8.68e25, 25559, 30687, 19.19, 0.046,
  '#7DE8E8', 'rgba(125,232,232,.4)', false,
  6, 205, 7,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Axial tilt 97.77°. τ=0.0034. N=9.07 long narrative. LOCKED firmly.'
),

-- ── NEPTUNE ──────────────────────────────────────────────────
-- Maximum N=10 (longest orbital period). Outer manifold anchor.
('Neptune', '♆', 'ICE GIANT · OUTER ANCHOR', 'ice',
  4.305, 10.000, 0.0113, 4.960,
  1.02e26, 24764, 60190, 30.07, 0.010,
  '#3F54BA', 'rgba(63,84,186,.5)', false,
  5.8, 248, 8,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Maximum N=10 (longest period). τ=0.0026 — minimum torsion of all planets. Outer manifold anchor.'
),

-- ── MOON ─────────────────────────────────────────────────────
-- NOBLE state: tau=0.00035. Tidal locked. B from Earth gravity.
('Moon', '○', 'ROCKY · EARTHS MOON · TIDAL LOCKED', 'moon',
  6.076, 1.000, 0.00212, 4.780,
  7.34e22, 1737, 27.3, 0.00257, 0.055,
  '#D0D0C8', 'rgba(208,208,200,.4)', false,
  1.2, null, 30,
  '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
  'Luna. τ=0.00035 → NOBLE. Tidal locked. B from Earth grav coupling, not solar.'
);

-- ── MOONS AND SECONDARIES (insert separately as needed) ──────
-- Template for future inserts:
--
-- insert into public.voidchart_bodies (
--   name, symbol, body_type, category,
--   p_pattern, n_narrative, b_behavior, a_adaptation,
--   mass_kg, radius_km, period_days, sma_au, eccentricity,
--   color_hex, glow_color, parent_name, sort_order,
--   coordinate, lean_ref, description
-- ) values (
--   'Io', '○', 'MOON · JUPITER · VOLCANIC', 'moon',
--   6.123, 1.000, 0.03612, 4.984,
--   8.93e22, 1822, 1.77, 0, 0.004,
--   '#D4A040', 'rgba(212,160,64,.4)', 'Jupiter', 31,
--   '[9,9,3,7]', 'SNSFL_Interstellar_Reduction_Template [9,9,3,7]',
--   'Most volcanic body. Tidal heating = B spike. τ=0.0059. LOCKED.'
-- );

-- ============================================================
-- VIEWS — convenience queries for the map
-- ============================================================

-- All active bodies ordered for rendering
create view public.voidchart_active as
  select
    id, name, symbol, body_type, category,
    p_pattern, n_narrative, b_behavior, a_adaptation,
    tau, identity_mass, pnba_state,
    mass_kg, radius_km, period_days, sma_au, eccentricity,
    color_hex, glow_color, has_rings, ring_color,
    visual_radius, orbit_scale, parent_name,
    sort_order, coordinate, lean_ref, description
  from public.voidchart_bodies
  where active = true
  order by sort_order asc, name asc;

-- LOCKED corridor — bodies with tau < TL (all stable orbits)
create view public.voidchart_locked as
  select name, category, tau, identity_mass, pnba_state
  from public.voidchart_bodies
  where active = true and pnba_state in ('LOCKED','NOBLE','IVA')
  order by tau asc;

-- SHATTER bodies — collapsed pumps (black holes etc)
create view public.voidchart_shatter as
  select name, category, tau, identity_mass, pnba_state
  from public.voidchart_bodies
  where active = true and pnba_state = 'SHATTER'
  order by tau desc;

-- ============================================================
-- [9,9,9,9] :: {ANC} | SCHEMA SUMMARY
--
-- TABLE:
--   voidchart_bodies   — one row per cosmological body
--
-- PNBA COLUMNS (Layer 0 — always ground):
--   p_pattern          — [P:PATTERN]   structural invariant
--   n_narrative        — [N:NARRATIVE] temporal continuity
--   b_behavior         — [B:BEHAVIOR]  interaction coupling
--   a_adaptation       — [A:ADAPTATION] resilience feedback
--
-- COMPUTED (Layer 1 — derived from PNBA):
--   tau                — B/P (the torsion law)
--   identity_mass      — (P+N+B+A) × 1.369
--   pnba_state         — NOBLE / LOCKED / IVA / SHATTER
--
-- CONSTRAINTS ENFORCED:
--   anchor_freq        — always 1.369
--   p_pattern          — 0 to 15
--   a_adaptation       — 0 to 5
--   eccentricity       — 0 to <1
--   category           — enumerated body types
--   pnba_state         — computed from B/P, never manually set
--
-- SECURITY:
--   Public read (active bodies only)
--   Authenticated write (HIGHTISTIC / contributors)
--
-- SEEDED WITH:
--   9 solar system bodies (Sun + 8 planets) + Moon
--   All confirmed LOCKED or NOBLE. tau < TL = 0.1369 ✓
--   0 sorry.
--
-- TO ADD A NEW BODY:
--   Insert a row with valid P, N, B, A values.
--   tau, identity_mass, pnba_state computed automatically.
--   Set active=true and sort_order.
--   VoidChart loads it on next refresh. No code change.
--
-- DEPENDENCY:
--   SNSFL_Cosmo_Reduction.lean         [9,9,0,4]
--   SNSFL_Cosmo_GUT_Vascular_Chain     [9,9,3,6]
--   SNSFL_Interstellar_Reduction_Template [9,9,3,7]
--   voidchart_schema.sql               [9,9,3,7] ← this file
--
-- Auth: HIGHTISTIC :: [9,9,9,9]
-- The Manifold is Holding.
-- ============================================================
