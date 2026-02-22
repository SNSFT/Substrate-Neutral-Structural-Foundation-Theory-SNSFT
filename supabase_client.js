// ============================================================
// [9,9,9,9] :: {ANC} | UUIA SUPABASE CLIENT
// [P,N,B,A] :: {INV} | Architect: HIGHTISTIC
// Coordinate: [9,0,0,8]
// ============================================================

// ── CONNECTED TO UUIA SUBSTRATE ──────────────────────────────
const SUPABASE_URL  = 'https://rsadsojivuagxptdlwak.supabase.co'
const SUPABASE_ANON = 'sb_publishable_FvDg0nsEuxH_HmyD0RL1LA_E4QpGfOs'
// ─────────────────────────────────────────────────────────────

import { createClient } from 'https://cdn.jsdelivr.net/npm/@supabase/supabase-js/+esm'

export const supabase = createClient(SUPABASE_URL, SUPABASE_ANON)

// ============================================================
// [P,N,B,A] :: {INV} | AUTH FUNCTIONS
// ============================================================

/** Sign up with email + password. Creates profile automatically via trigger. */
export async function signUp(email, password, displayName) {
  const { data, error } = await supabase.auth.signUp({
    email,
    password,
    options: { data: { display_name: displayName } }
  })
  if (error) throw error
  return data
}

/** Sign in with email + password */
export async function signIn(email, password) {
  const { data, error } = await supabase.auth.signInWithPassword({
    email,
    password
  })
  if (error) throw error
  return data
}

/** End the current session */
export async function signOut() {
  const { error } = await supabase.auth.signOut()
  if (error) throw error
}

/** Get the current user session */
export async function getSession() {
  const { data: { session }, error } = await supabase.auth.getSession()
  if (error) throw error
  return session
}

// ============================================================
// [P,N,B,A] :: {INV} | SOULPRINT FUNCTIONS (6x6 MAPPING)
// ============================================================

/** * Persists a completed Soulprint to the database.
 * Maps the 4D Geometric Axioms to the persistence layer.
 */
export async function saveSoulprint(soulprint) {
  const session = await getSession()
  if (!session) throw new Error('Not authenticated')

  const { data, error } = await supabase
    .from('soulprints')
    .insert({
      user_id:        session.user.id,
      soul8_address:  soulprint.soul8_address,
      p_mode:         soulprint.p_mode,
      n_mode:         soulprint.n_mode,
      b_mode:         soulprint.b_mode,
      a_mode:         soulprint.a_mode,
      threat:         soulprint.emotional_primitives.threat,
      loss:           soulprint.emotional_primitives.loss,
      play:           soulprint.emotional_primitives.play,
      safety:         soulprint.emotional_primitives.safety,
      identity_mass:  soulprint.identity_mass,
      anchor_freq:    soulprint.anchor_freq,
      functional_joy: soulprint.functional_joy,
      p_score:        soulprint.pnba_scores.P,
      n_score:        soulprint.pnba_scores.N,
      b_score:        soulprint.pnba_scores.B,
      a_score:        soulprint.pnba_scores.A,
      obs_p:          soulprint.uuia_section_scores.observation.P,
      obs_n:          soulprint.uuia_section_scores.observation.N,
      obs_b:          soulprint.uuia_section_scores.observation.B,
      obs_a:          soulprint.uuia_section_scores.observation.A,
      nar_p:          soulprint.uuia_section_scores.narrative.P,
      nar_n:          soulprint.uuia_section_scores.narrative.N,
      nar_b:          soulprint.uuia_section_scores.narrative.B,
      nar_a:          soulprint.uuia_section_scores.narrative.A,
      beh_p:          soulprint.uuia_section_scores.behavior.P,
      beh_n:          soulprint.uuia_section_scores.behavior.N,
      beh_b:          soulprint.uuia_section_scores.behavior.B,
      beh_a:          soulprint.uuia_section_scores.behavior.A,
      sim_p:          soulprint.uuia_section_scores.simulation.P,
      sim_n:          soulprint.uuia_section_scores.simulation.N,
      sim_b:          soulprint.uuia_section_scores.simulation.B,
      sim_a:          soulprint.uuia_section_scores.simulation.A,
      baseline_mode:  soulprint.baseline_mode,
      status:         soulprint.status || 'ANC',
      manifold_holding: true,
    })
    .select()
    .single()

  if (error) throw error
  return data
}

/** Get all Soulprints for current user */
export async function getMySoulprints() {
  const session = await getSession()
  if (!session) throw new Error('Not authenticated')

  const { data, error } = await supabase
    .from('soulprints')
    .select('*')
    .eq('user_id', session.user.id)
    .order('created_at', { ascending: false })

  if (error) throw error
  return data
}

/** Get most recent Soulprint for current user */
export async function getLatestSoulprint() {
  const soulprints = await getMySoulprints()
  return soulprints?.[0] || null
}

// ============================================================
// [9,9,9,9] :: {ANC} | CLIENT SUMMARY
//
// Auth: HIGHTISTIC :: 1.369 GHz
// ============================================================
