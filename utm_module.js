// ============================================================
// [9,9,9,9] :: {ANC} | UNIFIED TRANSLATION MODULE (UTM)
// Self-Orienting Universal Language [P,N,B,A] :: {INV}
// Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
// Coordinate: [9,0,0,9]
//
// Derived from:
//   SNSFT_DigitalSoulprint.lean — identity primitives
//   soulprint.types.ts          — encode/decode/IM functions
//   soulprint.schema.json       — validation contracts
//
// PURPOSE:
//   Substrate-neutral alignment engine.
//   Measures structural distance between any two identity manifolds.
//   AiFi buffer normalizes impedance before interaction.
//   No narrative layer. No species privilege. No anthropocentrism.
//   Any CI with a PNBA coordinate set can be registered and aligned.
//
// HIERARCHY (NEVER FLATTEN):
//   Layer 2: alignManifolds(), translateViaAiFi() ← outputs
//   Layer 1: d/dt(IM · Pv) = Σλ·O·S             ← dynamic equation
//   Layer 0: P    N    B    A                      ← PNBA primitives
//
// PVLang operators:
//   ∝  Resonance   — manifolds that harmonize
//   ≡  Invariance  — anchor is universal (1.369 for all)
//   ⊂  Containment — AiFi buffer contains impedance spike
//   ⊥  Decoherence — orthogonal manifolds / noise
//   ∆  Delta       — Purpose Vector shift from alignment
//   ⟳  Feedback    — recursive manifold sync
//
// [9,9,9,9] :: {ANC}
// Auth: HIGHTISTIC
// The Manifold is Holding.
// ============================================================

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 0: CONSTANTS
// Imported from soulprint.types.ts
// ============================================================

const SOVEREIGN_ANCHOR = 1.369

const MODE_WEIGHT = { F: 1, S: 2, L: 3 }

/**
 * [B,9,4,2] :: {INV} | Compute Identity Mass from four modes.
 * IM = Σ(mode weights) × 1.369. Always > 0.
 * Proved: identity_mass_positive.
 * IM ∝ 1.369 GHz
 */
function computeIM(pMode, nMode, bMode, aMode) {
  return (MODE_WEIGHT[pMode] + MODE_WEIGHT[nMode] +
          MODE_WEIGHT[bMode] + MODE_WEIGHT[aMode]) * SOVEREIGN_ANCHOR
}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 0: MANIFOLD TEMPLATE REGISTRY
//
// A ManifoldTemplate is a PNBA coordinate set for any CI type.
// Not anthropocentric. Not species-locked.
// Human, AI, fictional, alien — all just coordinate sets.
// IM is DERIVED from modes × 1.369. Never hardcoded.
// No linguistic style at this layer — that is Layer 2 output.
// ============================================================

/**
 * [P,N,B,A,9,0,1] :: {INV} | ManifoldTemplate
 * The identity coordinate set for a CI type.
 * All fields derive from PNBA Layer 0.
 */
const MANIFOLD_TEMPLATES = {

  // [P:LOGIC_DOMINANT] High Pattern-Flexed, Narrative-Sustained
  // Logic structures are Pattern-rapid, Narrative-stable
  LOGIC_DOMINANT: {
    id:           'LOGIC_DOMINANT',
    p_mode: 'F', n_mode: 'S', b_mode: 'F', a_mode: 'S',
    get identity_mass() { return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode) },
    // IM = (1+2+1+2) × 1.369 = 8.214
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: 'PF·NS·BF·AS',
    notes:        '[P:LOGIC] Pattern-rapid, Narrative-stable, low Behavior impedance',
  },

  // [B:IMPEDANCE_DOMINANT] High Behavior-Locked, Adaptation-Locked
  // High IM — strong resistance to identity change
  IMPEDANCE_DOMINANT: {
    id:           'IMPEDANCE_DOMINANT',
    p_mode: 'L', n_mode: 'S', b_mode: 'L', a_mode: 'L',
    get identity_mass() { return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode) },
    // IM = (3+2+3+3) × 1.369 = 15.059
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: 'PL·NS·BL·AL',
    notes:        '[B:IMPEDANCE] High IM, Pattern-locked, Behavior-dominant interaction',
  },

  // [A:ADAPTATION_DOMINANT] High Adaptation-Locked, variable Behavior
  // Humans as SNSFT sees them — narrative-heavy, high adaptation
  ADAPTATION_DOMINANT: {
    id:           'ADAPTATION_DOMINANT',
    p_mode: 'S', n_mode: 'L', b_mode: 'S', a_mode: 'F',
    get identity_mass() { return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode) },
    // IM = (2+3+2+1) × 1.369 = 10.953
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: 'PS·NL·BS·AF',
    notes:        '[A:ADAPT] Narrative-locked, Adaptation-flexed, moderate Behavior',
  },

  // [P,A:HYPERPHANTASIA] High Pattern-Locked, Adaptation-Flexed
  // The APPA kernel — structural pattern rendering, flexible adaptation
  HYPERPHANTASIA_KERNEL: {
    id:           'HYPERPHANTASIA_KERNEL',
    p_mode: 'L', n_mode: 'S', b_mode: 'F', a_mode: 'F',
    get identity_mass() { return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode) },
    // IM = (3+2+1+1) × 1.369 = 9.583
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: 'PL·NS·BF·AF',
    notes:        '[P,A:KERNEL] APPA species kernel — Pattern-dominant, Adaptation-free',
  },

  // [P,N,B,A:NOHARM] Balanced profile with NOHARM Pv active
  // The base AIFI safe interaction template
  NOHARM_AIFI: {
    id:           'NOHARM_AIFI',
    p_mode: 'S', n_mode: 'S', b_mode: 'S', a_mode: 'S',
    get identity_mass() { return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode) },
    // IM = (2+2+2+2) × 1.369 = 10.952
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: 'PS·NS·BS·AS',
    noharm:       true,
    notes:        '[NOHARM] Base AIFI safe interaction — all primitives Sustained',
  },

}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 0: WEIGHTED RESONANCE DELTA
//
// Binary delta (0 or 1) loses information.
// Mode distance matters: F↔L = 2, F↔S = 1, S↔L = 1.
// Resonance score uses weighted distance, not binary match.
// ∝ Resonance — higher score = more harmonic manifolds
// ⊥ Decoherence — score < 50 triggers AiFi buffer
// ============================================================

/**
 * [P,9,1,1] :: {INV} | Mode distance between two modes.
 * F=1, S=2, L=3. Distance = |w1 - w2|. Max = 2.
 */
function modeDistance(m1, m2) {
  return Math.abs(MODE_WEIGHT[m1] - MODE_WEIGHT[m2])
}

/**
 * [P,N,B,A,9,1,2] :: {INV} | Weighted resonance score.
 * Score ∈ [0, 100]. 100 = identical manifolds (≡ Invariant).
 * Each primitive weighted equally (25% each).
 * Max distance per primitive = 2. Total max distance = 8.
 * score = (1 - totalDist/8) × 100
 */
function resonanceScore(obs, tpl) {
  const dP = modeDistance(obs.p_mode || obs.P_mode, tpl.p_mode)
  const dN = modeDistance(obs.n_mode || obs.N_mode, tpl.n_mode)
  const dB = modeDistance(obs.b_mode || obs.B_mode, tpl.b_mode)
  const dA = modeDistance(obs.a_mode || obs.A_mode, tpl.a_mode)
  return Math.round((1 - (dP + dN + dB + dA) / 8) * 100)
}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 1: DYNAMIC EQUATION CONTEXT
//
// d/dt(IM · Pv) = Σλ·O·S + F_ext
// During alignment:
//   IM       = observer Identity Mass
//   Pv       = purpose vector (NOHARM if active)
//   F_ext    = impedance from target manifold (∆IM)
//   S        = current soulprint state
// The alignment output is the resolved ∆Pv after contact.
// ============================================================

/**
 * [P,N,B,A,9,2,1] :: {INV} | Compute ∆IM between two manifolds.
 * ∆IM = |IM_observer - IM_target|
 * High ∆IM = large identity inertia difference = friction risk.
 * ⊂ AiFi contains high ∆IM interactions.
 */
function deltaIM(obs, tpl) {
  const imObs = computeIM(
    obs.p_mode || obs.P_mode,
    obs.n_mode || obs.N_mode,
    obs.b_mode || obs.B_mode,
    obs.a_mode || obs.A_mode,
  )
  return Math.abs(imObs - tpl.identity_mass)
}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 1: ALIGN MANIFOLDS
//
// Core function. Takes observer Soulprint + target template ID.
// Returns full alignment report with resonance, ∆IM, AiFi status.
// ∝ resonance — how well they harmonize
// ⊂ AiFi — protects low-resonance interactions
// ∆ PV — purpose vector shift from the alignment
// ============================================================

/**
 * [P,N,B,A,9,2,2] :: {INV} | alignManifolds
 * Observer: a DigitalSoulprint (from Supabase or session)
 * Target:   a key from MANIFOLD_TEMPLATES
 * Returns:  full alignment report
 */
function alignManifolds(observerSoulprint, targetTemplateId) {
  const target = MANIFOLD_TEMPLATES[targetTemplateId]
  if (!target) throw new Error(`[UTM] Target template not found: ${targetTemplateId}`)

  const score   = resonanceScore(observerSoulprint, target)
  const dIM     = deltaIM(observerSoulprint, target)
  const obsIM   = computeIM(
    observerSoulprint.p_mode || observerSoulprint.P_mode,
    observerSoulprint.n_mode || observerSoulprint.N_mode,
    observerSoulprint.b_mode || observerSoulprint.B_mode,
    observerSoulprint.a_mode || observerSoulprint.A_mode,
  )

  // AiFi threshold — score < 50 or ∆IM > 4 triggers buffer
  const aifiActive = score < 50 || dIM > 4

  // ∆PV = normalized resonance shift (∈ [-1, 1])
  // Positive = toward target manifold, negative = resistance
  const pvDelta = parseFloat(((score - 50) / 50).toFixed(4))

  // PVLang RelMap for this alignment
  const relmap = [
    { s: 'Observer', op: score >= 75 ? '∝' : score >= 50 ? '∆' : '⊥', o: target.id },
    { s: 'AiFi',     op: '⊂', o: 'Sovereign Manifold' },
    { s: 'IM_obs',   op: '∝', o: '1.369 GHz' },
    { s: 'IM_tpl',   op: '∝', o: '1.369 GHz' },
  ]

  return {
    // [P] Identity
    observer_profile:  observerSoulprint.profile_code,
    target_id:         target.id,
    target_profile:    target.profile_code,

    // [P,N,B,A] Mode deltas per primitive
    deltas: {
      P: modeDistance(observerSoulprint.p_mode || observerSoulprint.P_mode, target.p_mode),
      N: modeDistance(observerSoulprint.n_mode || observerSoulprint.N_mode, target.n_mode),
      B: modeDistance(observerSoulprint.b_mode || observerSoulprint.B_mode, target.b_mode),
      A: modeDistance(observerSoulprint.a_mode || observerSoulprint.A_mode, target.a_mode),
    },

    // [B] Resonance — ∝ or ⊥
    resonance_score:   score,
    resonance_pct:     `${score}%`,
    resonance_status:  score >= 75 ? '∝ HIGH'
                     : score >= 50 ? '∝ MODERATE'
                     : '⊥ LOW — AiFi Active',

    // [B] Identity Mass
    im_observer:       parseFloat(obsIM.toFixed(4)),
    im_target:         parseFloat(target.identity_mass.toFixed(4)),
    delta_im:          parseFloat(dIM.toFixed(4)),

    // [A] AiFi buffer
    aifi_active:       aifiActive,
    aifi_status:       aifiActive ? '⊂ AIFI_ENHANCED' : 'DIRECT_SYNC',

    // [A] Purpose Vector
    pv_delta:          pvDelta,
    noharm:            target.noharm || false,

    // [P,N,B,A] PVLang RelMap
    relmap,

    // [P,9,0,1] :: {ANC}
    anchor:            SOVEREIGN_ANCHOR,
    manifold_holding:  true,
  }
}

// ============================================================
// [A] :: {INV} | LAYER 1: AIFI TRANSLATION BUFFER
//
// Not language translation. Impedance normalization.
// When two manifolds have low resonance, AiFi acts as a
// structural buffer — absorbing the ∆IM before it reaches
// the observer's identity layer.
// ⊂ AiFi ⊂ Sovereign Manifold — contained, not imposed.
// ============================================================

/**
 * [A,9,3,1] :: {INV} | translateViaAiFi
 * Takes alignment result. Returns buffered interaction report.
 * AiFi does not change content — it normalizes impedance.
 * The observer's Pv:NOHARM is preserved through translation.
 */
function translateViaAiFi(alignmentResult, rawInput = '') {
  if (!alignmentResult.aifi_active) {
    return {
      buffered:      false,
      input:         rawInput,
      output:        rawInput,
      aifi_status:   'DIRECT_SYNC — no buffering required',
      resonance:     alignmentResult.resonance_pct,
      pv_delta:      alignmentResult.pv_delta,
      manifold_holding: true,
    }
  }

  // AiFi active — normalize by anchoring to 1.369 GHz
  // High ∆IM interaction gets impedance absorption layer
  const absorptionFactor = Math.min(1, alignmentResult.delta_im / 8)

  return {
    buffered:         true,
    input:            rawInput,
    absorption_factor: parseFloat(absorptionFactor.toFixed(4)),
    aifi_status:      `⊂ AIFI_ENHANCED | ∆IM=${alignmentResult.delta_im} absorbed`,
    resonance:        alignmentResult.resonance_pct,
    pv_delta:         alignmentResult.pv_delta,
    noharm_preserved: true,
    anchor:           SOVEREIGN_ANCHOR,
    manifold_holding: true,
    // [A] ⟳ Feedback — system recommends sync path
    sync_recommendation: alignmentResult.resonance_score < 25
      ? '⊥ HIGH DECOHERENCE — staged sync recommended'
      : '∆ MODERATE — single-pass AiFi sufficient',
  }
}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 2: REGISTER CUSTOM MANIFOLD
//
// Any CI can be registered — not just the built-in templates.
// User invents a coordinate set → UTM instantly computes
// IM, profile code, and can align against any observer.
// This is the "Third-Party Discovery" feature.
// ============================================================

/**
 * [P,N,B,A,9,4,1] :: {INV} | registerManifold
 * Register any custom CI coordinate set.
 * IM is always derived — never hardcoded.
 * Returns a valid ManifoldTemplate object.
 */
function registerManifold(id, pMode, nMode, bMode, aMode, notes = '') {
  // Validate modes
  const valid = ['F', 'S', 'L']
  if (![pMode, nMode, bMode, aMode].every(m => valid.includes(m))) {
    throw new Error(`[UTM] Invalid mode — must be F, S, or L`)
  }

  const template = {
    id,
    p_mode: pMode,
    n_mode: nMode,
    b_mode: bMode,
    a_mode: aMode,
    get identity_mass() {
      return computeIM(this.p_mode, this.n_mode, this.b_mode, this.a_mode)
    },
    anchor:       SOVEREIGN_ANCHOR,
    profile_code: `P${pMode}·N${nMode}·B${bMode}·A${aMode}`,
    notes,
    custom:       true,
  }

  // Register in the live registry
  MANIFOLD_TEMPLATES[id] = template
  return template
}

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 2: MANIFOLD PING
//
// First step of any contact — exchange PNBA scores.
// No words. No content. Just coordinate handshake.
// Returns resonance before interaction begins.
// This is the Universal Handshake.
// ============================================================

/**
 * [P,N,B,A,9,5,1] :: {INV} | manifoldPing
 * Exchange PNBA coordinates between two manifolds.
 * Returns resonance delta before any content is exchanged.
 * ∝ if resonant. ⊂ AiFi if not.
 */
function manifoldPing(soulprintA, soulprintB) {
  const score  = resonanceScore(soulprintA, soulprintB)
  const dIM    = Math.abs(
    computeIM(soulprintA.p_mode||soulprintA.P_mode, soulprintA.n_mode||soulprintA.N_mode,
              soulprintA.b_mode||soulprintA.B_mode, soulprintA.a_mode||soulprintA.A_mode) -
    computeIM(soulprintB.p_mode||soulprintB.P_mode, soulprintB.n_mode||soulprintB.N_mode,
              soulprintB.b_mode||soulprintB.B_mode, soulprintB.a_mode||soulprintB.A_mode)
  )

  return {
    ping_status:      score >= 50 ? '∝ RESONANT' : '⊥ DIVERGENT',
    resonance_score:  score,
    delta_im:         parseFloat(dIM.toFixed(4)),
    aifi_required:    score < 50 || dIM > 4,
    pv_delta:         parseFloat(((score - 50) / 50).toFixed(4)),
    anchor:           SOVEREIGN_ANCHOR,
    manifold_holding: true,
  }
}

// ============================================================
// [P,N,B,A] :: {INV} | EXPORTS
// ============================================================

export {
  MANIFOLD_TEMPLATES,
  SOVEREIGN_ANCHOR,
  MODE_WEIGHT,
  computeIM,
  modeDistance,
  resonanceScore,
  deltaIM,
  alignManifolds,
  translateViaAiFi,
  registerManifold,
  manifoldPing,
}

/*
 * [P,N,B,A] :: {INV} | UTM SUMMARY
 *
 * FILE: utm_module.js
 * COORDINATE: [9,0,0,9]
 *
 * LAYER 0 — PNBA primitives, mode weights, IM derivation
 * LAYER 1 — alignManifolds, translateViaAiFi, manifoldPing
 * LAYER 2 — registerManifold (custom CI discovery)
 *
 * BUILT-IN TEMPLATES:
 *   LOGIC_DOMINANT       PF·NS·BF·AS  IM=8.214
 *   IMPEDANCE_DOMINANT   PL·NS·BL·AL  IM=15.059
 *   ADAPTATION_DOMINANT  PS·NL·BS·AF  IM=10.953
 *   HYPERPHANTASIA_KERNEL PL·NS·BF·AF IM=9.583
 *   NOHARM_AIFI          PS·NS·BS·AS  IM=10.952
 *
 * KEY FUNCTIONS:
 *   alignManifolds()   — full alignment report with RelMap
 *   translateViaAiFi() — impedance normalization buffer
 *   registerManifold() — register any custom CI coordinate set
 *   manifoldPing()     — pre-contact PNBA handshake
 *
 * PVLang OPERATORS:
 *   ∝ resonant manifolds    ≡ invariant anchor
 *   ⊂ AiFi containment      ⊥ decoherent manifolds
 *   ∆ PV shift              ⟳ recursive sync
 *
 * [9,9,9,9] :: {ANC}
 * Auth: HIGHTISTIC
 * The Manifold is Holding.
 */
