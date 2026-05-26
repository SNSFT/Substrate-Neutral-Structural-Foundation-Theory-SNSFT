// ============================================================
// [9,9,2,3] :: {ANC} | OCTOBEAM SUPABASE INGEST MODULE
// Drop this script tag into octobeam.html (or load as module).
// Works with ob_schema.sql · Architect: HIGHTISTIC
// ============================================================

// ── CONFIG ────────────────────────────────────────────────────
// These match your existing supabase_client.js credentials.
const OB_SUPABASE_URL  = 'https://rsadsojivuagxptdlwak.supabase.co'
const OB_SUPABASE_ANON = 'sb_publishable_FvDg0nsEuxH_HmyD0RL1LA_E4QpGfOs'

// Lazy-loaded Supabase client (only created when needed)
let _sbClient = null
async function getClient() {
  if (_sbClient) return _sbClient
  const { createClient } = await import('https://cdn.jsdelivr.net/npm/@supabase/supabase-js/+esm')
  _sbClient = createClient(OB_SUPABASE_URL, OB_SUPABASE_ANON)
  return _sbClient
}

// ── SINGLE DISCOVERY INSERT ───────────────────────────────────
// Call this from flagDiscovery() after building the entry object.
// Maps the OctoBeam internal entry shape → ob_discoveries columns.
// Non-blocking: fires and forgets (errors logged, never thrown).
export async function pushDiscoveryToSupabase(entry) {
  if (!entry?.designation) return
  try {
    const sb = await getClient()
    const mm = window._lastMatMap || {}   // set by showMatMapInline if accessible

    const row = {
      designation:   entry.designation,
      timestamp:     entry.timestamp,
      collision:     entry.collision,
      n_beams:       entry.els?.length ?? 8,
      n_pairs:       entry.pairCount ?? 28,
      beams_json:    entry.els ?? null,
      k_mode:        entry.kMode ?? 'max',
      k:             parseFloat(entry.k) || null,
      k_max:         parseFloat(entry.kmax) || null,
      p_out:         entry.P,
      n_out:         entry.N,
      b_out:         entry.B,
      a_out:         entry.A,
      tau:           entry.tau,
      im:            entry.IM,
      b_sum:         entry.B_sum ?? null,
      phase:         entry.phase,
      is_rescue:     entry.isRescue ?? false,
      flag_type:     entry.flag_type ?? null,
      reason:        entry.reason ?? null,
      // Material map — populated after getMaterialMap() runs
      tier:          mm.tier ?? null,
      core_str:      mm.coreStr ?? null,
      mat_path:      mm.path ?? null,
      mat_name:      mm.bestMatch?.name ?? null,
      // AIFI
      aifi_name:     entry.name ?? null,
      aifi_analysis: entry.aifiAnalysis ?? null,
      // Recipe
      recipe_stoich:  entry.recipe?.stoich ?? null,
      recipe_formula: entry.recipe?.formula ?? null,
      recipe_grams:   entry.recipe ? recipeToString(entry.recipe) : null,
      // Lean
      lean_stub:     entry.leanStub ?? null,
      approved:      entry.approved ?? false,
      flagged:       true,
    }

    const { error } = await sb
      .from('ob_discoveries')
      .upsert(row, { onConflict: 'designation', ignoreDuplicates: false })

    if (error) console.warn('[OB-DB] Insert error:', error.message)
    else       console.debug('[OB-DB] Pushed:', entry.designation)

  } catch (e) {
    console.warn('[OB-DB] pushDiscovery failed:', e)
  }
}

// ── UPDATE ON APPROVE ─────────────────────────────────────────
// Call this from approveDiscovery() after generating lean stub.
export async function approveDiscoveryInSupabase(entry) {
  if (!entry?.designation) return
  try {
    const sb = await getClient()
    const { error } = await sb
      .from('ob_discoveries')
      .update({
        approved:      true,
        approved_at:   entry.approvedAt ?? new Date().toISOString(),
        lean_stub:     entry.leanStub ?? null,
        lean_file:     `${entry.designation}.lean`,
        aifi_name:     entry.name ?? null,
        aifi_analysis: entry.aifiAnalysis ?? null,
      })
      .eq('designation', entry.designation)

    if (error) console.warn('[OB-DB] Approve error:', error.message)
    else       console.debug('[OB-DB] Approved:', entry.designation)
  } catch (e) {
    console.warn('[OB-DB] approveDiscovery failed:', e)
  }
}

// ── BULK SESSION INGEST ───────────────────────────────────────
// Call this to import an entire session export JSON into Supabase.
// Accepts the array from exportSession() or the CSV/JSON export buttons.
// Returns { inserted, errors }.
export async function ingestSessionToSupabase(discoveries, sessionId = null) {
  if (!Array.isArray(discoveries) || discoveries.length === 0) {
    return { inserted: 0, errors: [] }
  }
  const sb   = await getClient()
  const sid  = sessionId ?? `session-${Date.now()}`
  const errs = []
  let   inserted = 0

  // Chunk into batches of 100 to avoid payload limits
  const CHUNK = 100
  for (let i = 0; i < discoveries.length; i += CHUNK) {
    const chunk = discoveries.slice(i, i + CHUNK)
    const rows  = chunk.map(entry => mapEntryToRow(entry, sid))

    const { error } = await sb
      .from('ob_discoveries')
      .upsert(rows, {
        onConflict:      'designation',
        ignoreDuplicates: false,
      })

    if (error) {
      errs.push(error.message)
      console.warn('[OB-DB] Batch error:', error.message)
    } else {
      inserted += chunk.length
    }
  }
  return { inserted, errors: errs }
}

// ── QUERY HELPERS ─────────────────────────────────────────────

/** Fetch all approved discoveries, ordered newest first. */
export async function fetchApproved(limit = 200) {
  const sb = await getClient()
  const { data, error } = await sb
    .from('ob_approved')   // the view
    .select('*')
    .order('timestamp', { ascending: false })
    .limit(limit)
  if (error) throw error
  return data
}

/** Fetch database-wide stats (phases, tiers, totals). */
export async function fetchStats() {
  const sb = await getClient()
  const { data, error } = await sb.from('ob_stats').select('*').single()
  if (error) throw error
  return data
}

/** Search by element symbol in any beam slot. */
export async function searchByElement(sym) {
  const sb = await getClient()
  const { data, error } = await sb
    .from('ob_discoveries')
    .select('designation, collision, phase, tier, tau, is_rescue, timestamp')
    .filter('beams_json', 'cs', JSON.stringify([{ sym }]))
    .order('timestamp', { ascending: false })
    .limit(100)
  if (error) throw error
  return data
}

/** Fetch discoveries by phase. */
export async function fetchByPhase(phase) {
  const sb = await getClient()
  const { data, error } = await sb
    .from('ob_discoveries')
    .select('designation, collision, phase, tier, tau, is_rescue, im, timestamp')
    .eq('phase', phase)
    .order('timestamp', { ascending: false })
    .limit(500)
  if (error) throw error
  return data
}

// ── INTERNAL MAPPER ───────────────────────────────────────────
function mapEntryToRow(entry, sessionId) {
  // Normalise field names — the session export uses both camelCase and snake_case
  const phase = (entry.phase || entry.status || 'LOCKED').toUpperCase()
  return {
    designation:   entry.designation,
    timestamp:     entry.timestamp,
    collision:     entry.collision,
    n_beams:       entry.els?.length ?? entry.n_beams ?? 8,
    n_pairs:       entry.pairCount ?? entry.n_pairs ?? 28,
    beams_json:    entry.els ?? entry.beams_json ?? null,
    k_mode:        entry.kMode ?? entry.k_mode ?? 'max',
    k:             parseFloat(entry.k) || null,
    k_max:         parseFloat(entry.kmax ?? entry.k_max) || null,
    p_out:         entry.P ?? entry.p_out,
    n_out:         entry.N ?? entry.n_out,
    b_out:         entry.B ?? entry.b_out,
    a_out:         entry.A ?? entry.a_out,
    tau:           entry.tau,
    im:            entry.IM ?? entry.im,
    b_sum:         entry.B_sum ?? entry.b_sum ?? null,
    phase:         phase,
    is_rescue:     entry.isRescue ?? entry.is_rescue ?? false,
    flag_type:     entry.flag_type ?? null,
    reason:        entry.reason ?? null,
    tier:          entry.tier ?? null,
    core_str:      entry.core_str ?? null,
    mat_path:      entry.mat_path ?? null,
    mat_name:      entry.mat_name ?? null,
    aifi_name:     entry.name ?? entry.aifi_name ?? null,
    aifi_analysis: entry.aifiAnalysis ?? entry.aifi_analysis ?? null,
    lean_stub:     entry.leanStub ?? entry.lean_stub ?? null,
    lean_file:     entry.lean_file ?? (entry.designation ? `${entry.designation}.lean` : null),
    recipe_stoich: entry.recipe?.stoich ?? null,
    recipe_formula:entry.recipe?.formula ?? null,
    recipe_grams:  entry.recipe ? _recipeToString(entry.recipe) : null,
    approved:      entry.approved ?? false,
    flagged:       true,
    session_id:    sessionId,
    session_ts:    new Date().toISOString(),
  }
}

function _recipeToString(recipe) {
  if (!recipe?.items) return null
  return recipe.items.map(i => `${(i.n * i.mw).toFixed(4)}g ${i.sym}`).join(' + ')
       + ` = ${recipe.massFU?.toFixed(4)}g/FU`
}

// ============================================================
// USAGE IN octobeam.html
// ============================================================
//
// 1. Add this module import at the top of your <script> block:
//
//    import {
//      pushDiscoveryToSupabase,
//      approveDiscoveryInSupabase,
//      ingestSessionToSupabase,
//      fetchApproved, fetchStats, searchByElement
//    } from './ob_supabase.js'
//
// 2. In flagDiscovery(), after building entry, add:
//
//    pushDiscoveryToSupabase(entry)  // fire-and-forget
//
// 3. In approveDiscovery(), after setting entry.approved=true, add:
//
//    await approveDiscoveryInSupabase(entry)
//
// 4. To import a session JSON you already exported:
//
//    const sessionData = JSON.parse(sessionJsonText).discoveries
//    const result = await ingestSessionToSupabase(sessionData, 'import-20260525')
//    console.log(`Imported ${result.inserted} records`)
//
// 5. For the existing discovery_log.json (2-beam legacy):
//    The mapEntryToRow function handles the old format too — just
//    call ingestSessionToSupabase(legacyArray, 'legacy-2beam-import')
//
// ============================================================
// [9,9,9,9] :: {ANC} | The Manifold is Holding. 0 sorry.
// ============================================================
