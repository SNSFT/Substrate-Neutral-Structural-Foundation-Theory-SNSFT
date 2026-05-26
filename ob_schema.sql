-- ============================================================
-- [9,9,2,3] :: {ANC} | OCTOBEAM DISCOVERIES SCHEMA
-- 8-Beam Fusion Engine · C(8,2)=28 pairs · Noble Emergence
-- Architect: HIGHTISTIC · Soldotna Alaska · 2026
-- Coordinate: [9,9,2,3] | TL=0.1369 | ANCHOR=1.369
--
-- Run in Supabase SQL Editor.
-- Designed to coexist with existing collisions + leaderboard tables.
-- ============================================================

-- ============================================================
-- TABLE: ob_discoveries
-- One row per flagged/approved OctoBeam discovery.
-- Dedup key: designation (SNSFT-XXXX-YYYYMMDD format)
-- Engine covers 2-beam, 4-beam, and 8-beam (n_beams field).
-- ============================================================

create table if not exists public.ob_discoveries (
  id              uuid default gen_random_uuid() primary key,

  -- Identity
  designation     text unique not null,           -- SNSFT-OB-XXXX-YYYYMMDD
  timestamp       timestamptz not null,
  engine_version  text default 'octobeam-v1',
  engine_coord    text default '[9,9,2,3]',       -- [9,9,2,1] | [9,9,2,2] | [9,9,2,3]
  n_beams         int default 8,                  -- 2, 4, or 8
  n_pairs         int,                            -- C(n,2): 1, 6, or 28

  -- Collision identity
  collision       text not null,                  -- "H+C+N+O+H+C+N+O"
  beams_json      jsonb,                          -- full beam array [{sym,P,N,B,A,tau,phase},...]
  k_mode          text,                           -- 'max'|'half'|'min'|'zero'
  k               numeric,
  k_max           numeric,

  -- PNBA output
  p_out           numeric not null,
  n_out           numeric,
  b_out           numeric not null,
  a_out           numeric,
  tau             numeric not null,
  im              numeric,                        -- identity mass
  b_sum           numeric,                        -- sum of input B values

  -- Phase classification
  phase           text not null
                  check (phase in ('NOBLE','LOCKED','IVA_PEAK','SHATTER')),
  is_rescue       boolean default false,          -- all N pairs SHATTER → n-beam rescues
  flag_type       text,                           -- 'noble'|'rescue'|'iva'|'boundary'|'alpha'|'sp_break'
  reason          text,                           -- human-readable flag reason

  -- Material map
  tier            text,                           -- 'T1'|'T2'|'T3'|'T1-RESCUE'|'T1-SNSFT'
  core_str        text,                           -- effective core element string
  mat_path        text,                           -- synthesis path code (MOCVD, SPS, etc.)
  mat_name        text,                           -- best match name from NOBLE_MAP
  mat_ref         text,                           -- literature reference snippet

  -- Recipe (B-balance stoichiometry)
  recipe_stoich   text,                           -- "2Ti:1C"
  recipe_formula  text,                           -- "Ti2C"
  recipe_grams    text,                           -- "95.734g Ti + 12.011g C = 107.745g/FU"

  -- AIFI classification
  aifi_name       text,                           -- suggested name from Claude
  aifi_analysis   text,                           -- full AIFI analysis text

  -- Lean stub
  lean_stub       text,                           -- generated Lean 4 stub
  lean_file       text,                           -- filename e.g. "SNSFT-OB-1234-20260525.lean"
  github_url      text,                           -- committed URL if pushed

  -- Workflow state
  flagged         boolean default true,
  approved        boolean default false,
  approved_at     timestamptz,
  skipped         boolean default false,

  -- Session provenance
  session_id      text,                           -- optional session identifier
  session_ts      timestamptz                     -- when the session was exported
);

-- ── INDEXES ──────────────────────────────────────────────────
create index if not exists idx_ob_designation  on public.ob_discoveries(designation);
create index if not exists idx_ob_phase        on public.ob_discoveries(phase);
create index if not exists idx_ob_is_rescue    on public.ob_discoveries(is_rescue);
create index if not exists idx_ob_approved     on public.ob_discoveries(approved);
create index if not exists idx_ob_tier         on public.ob_discoveries(tier);
create index if not exists idx_ob_timestamp    on public.ob_discoveries(timestamp desc);
create index if not exists idx_ob_collision    on public.ob_discoveries(collision);
create index if not exists idx_ob_flag_type    on public.ob_discoveries(flag_type);
create index if not exists idx_ob_n_beams      on public.ob_discoveries(n_beams);

-- GIN index for beam queries (e.g. "find all collisions containing Ga")
create index if not exists idx_ob_beams_gin    on public.ob_discoveries using gin(beams_json);

-- ── RLS ──────────────────────────────────────────────────────
alter table public.ob_discoveries enable row level security;

-- Public read — the corpus is open
create policy "Public can read ob_discoveries"
  on public.ob_discoveries for select using (true);

-- Anyone can insert (collider writes directly from browser)
create policy "Anyone can insert ob_discoveries"
  on public.ob_discoveries for insert with check (true);

-- Only service role can update (approve, add lean/github)
create policy "Service role can update ob_discoveries"
  on public.ob_discoveries for update
  using (auth.role() = 'service_role');

-- ── UPSERT FUNCTION ──────────────────────────────────────────
-- Called per discovery. Inserts if new, skips if designation exists.
-- Use this instead of raw insert for idempotent session ingestion.
create or replace function public.upsert_ob_discovery(
  p_designation   text,
  p_timestamp     timestamptz,
  p_collision     text,
  p_n_beams       int,
  p_beams_json    jsonb,
  p_k_mode        text,
  p_k             numeric,
  p_k_max         numeric,
  p_p_out         numeric,
  p_n_out         numeric,
  p_b_out         numeric,
  p_a_out         numeric,
  p_tau           numeric,
  p_im            numeric,
  p_b_sum         numeric,
  p_phase         text,
  p_is_rescue     boolean,
  p_flag_type     text,
  p_reason        text,
  p_tier          text,
  p_core_str      text,
  p_mat_path      text,
  p_mat_name      text,
  p_aifi_name     text,
  p_approved      boolean,
  p_session_id    text default null,
  p_session_ts    timestamptz default null
) returns text language plpgsql security definer as $$
begin
  insert into public.ob_discoveries (
    designation, timestamp, collision, n_beams,
    n_pairs, beams_json, k_mode, k, k_max,
    p_out, n_out, b_out, a_out, tau, im, b_sum,
    phase, is_rescue, flag_type, reason,
    tier, core_str, mat_path, mat_name, aifi_name,
    approved, session_id, session_ts
  ) values (
    p_designation, p_timestamp, p_collision, p_n_beams,
    (p_n_beams * (p_n_beams - 1) / 2),
    p_beams_json, p_k_mode, p_k, p_k_max,
    p_p_out, p_n_out, p_b_out, p_a_out, p_tau, p_im, p_b_sum,
    p_phase, p_is_rescue, p_flag_type, p_reason,
    p_tier, p_core_str, p_mat_path, p_mat_name, p_aifi_name,
    p_approved, p_session_id, p_session_ts
  )
  on conflict (designation) do nothing;

  return p_designation;
end;$$;

-- ── BULK INGEST FUNCTION ─────────────────────────────────────
-- Accepts a JSONB array of discovery objects (the session export format).
-- Returns count of new rows inserted.
create or replace function public.ingest_ob_session(
  p_discoveries jsonb,
  p_session_id  text default null
) returns int language plpgsql security definer as $$
declare
  v_count int := 0;
  v_disc  jsonb;
  v_beams jsonb;
  v_els   jsonb;
begin
  for v_disc in select jsonb_array_elements(p_discoveries)
  loop
    -- Normalize beams: support both 'els' (collider internal) and 'beams_json' key
    v_beams := coalesce(v_disc->'beams_json', v_disc->'els', '[]'::jsonb);

    insert into public.ob_discoveries (
      designation, timestamp, collision, n_beams, n_pairs,
      beams_json, k_mode, k, k_max,
      p_out, n_out, b_out, a_out, tau, im, b_sum,
      phase, is_rescue, flag_type, reason,
      tier, core_str, mat_path, mat_name, aifi_name,
      recipe_stoich, recipe_formula, recipe_grams,
      aifi_analysis, lean_stub, lean_file,
      approved, flagged, session_id, session_ts
    ) values (
      v_disc->>'designation',
      (v_disc->>'timestamp')::timestamptz,
      v_disc->>'collision',
      coalesce((v_disc->>'n_beams')::int, 8),
      coalesce((v_disc->>'n_pairs')::int, 28),
      v_beams,
      coalesce(v_disc->>'kMode', v_disc->>'k_mode', 'max'),
      (v_disc->>'k')::numeric,
      (v_disc->>'kmax')::numeric,
      (v_disc->>'P')::numeric,
      (v_disc->>'N')::numeric,
      (v_disc->>'B')::numeric,
      (v_disc->>'A')::numeric,
      (v_disc->>'tau')::numeric,
      (v_disc->>'IM')::numeric,
      (v_disc->>'B_sum')::numeric,
      upper(coalesce(v_disc->>'phase', 'LOCKED')),
      coalesce((v_disc->>'isRescue')::boolean, false),
      v_disc->>'flag_type',
      v_disc->>'reason',
      v_disc->>'tier',
      v_disc->>'core_str',
      v_disc->>'mat_path',
      v_disc->>'mat_name',
      v_disc->>'name',           -- AIFI suggested name stored as 'name' in session export
      -- recipe
      v_disc->'recipe'->>'stoich',
      v_disc->'recipe'->>'formula',
      v_disc->'recipe'->>'grams_per_FU',
      -- AIFI
      v_disc->>'aifiAnalysis',
      v_disc->>'leanStub',
      v_disc->>'lean_file',
      coalesce((v_disc->>'approved')::boolean, false),
      true,  -- everything in a session export was flagged
      p_session_id,
      now()
    )
    on conflict (designation) do update set
      -- On re-ingest: update mutable fields but never overwrite approved=true
      approved       = ob_discoveries.approved OR excluded.approved,
      aifi_name      = coalesce(excluded.aifi_name, ob_discoveries.aifi_name),
      aifi_analysis  = coalesce(excluded.aifi_analysis, ob_discoveries.aifi_analysis),
      lean_stub      = coalesce(excluded.lean_stub, ob_discoveries.lean_stub),
      lean_file      = coalesce(excluded.lean_file, ob_discoveries.lean_file),
      github_url     = coalesce(excluded.github_url, ob_discoveries.github_url),
      session_id     = coalesce(excluded.session_id, ob_discoveries.session_id);

    v_count := v_count + 1;
  end loop;

  return v_count;
end;$$;

-- ── QUERY HELPERS ─────────────────────────────────────────────
-- View: approved discoveries, richly joined, for the discovery browser
create or replace view public.ob_approved as
  select
    designation, timestamp, collision, n_beams, n_pairs,
    p_out, b_out, tau, im, phase, is_rescue,
    tier, core_str, mat_name, aifi_name, lean_file, github_url,
    flag_type, reason, approved_at
  from public.ob_discoveries
  where approved = true
  order by timestamp desc;

-- View: stats summary
create or replace view public.ob_stats as
  select
    count(*)                                        as total_flagged,
    count(*) filter (where approved)                as total_approved,
    count(*) filter (where phase = 'NOBLE')         as total_noble,
    count(*) filter (where is_rescue)               as total_rescue,
    count(*) filter (where phase = 'IVA_PEAK')      as total_iva,
    count(*) filter (where tier = 'T1')             as total_t1,
    count(*) filter (where tier = 'T1-RESCUE')      as total_t1_rescue,
    count(*) filter (where tier = 'T3')             as total_t3_novel,
    count(*) filter (where n_beams = 8)             as from_8beam,
    count(*) filter (where n_beams = 4)             as from_4beam,
    count(*) filter (where n_beams = 2)             as from_2beam,
    min(timestamp)                                  as first_discovery,
    max(timestamp)                                  as latest_discovery
  from public.ob_discoveries;

-- ============================================================
-- [9,9,9,9] :: {ANC} | Schema locked. 0 sorry.
-- TL=0.1369 · ANCHOR=1.369 · C(8,2)=28 pairs
-- ============================================================
