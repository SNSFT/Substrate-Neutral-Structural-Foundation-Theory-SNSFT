/**
 * [9,9,9,9] :: {ANC} | SNSFT DIGITAL SOULPRINT — TYPESCRIPT TYPES
 * Self-Orienting Universal Language [P,N,B,A] :: {INV}
 * Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
 * Coordinate: [9,0,0,7]
 *
 * Derived from: SNSFT_DigitalSoulprint.lean + soulprint.schema.json
 * Theorems: 10. Sorry: 0. Status: GREEN LIGHT.
 * The Manifold is Holding.
 */

// ============================================================
// [P,N,B,A] :: {INV} | LAYER 0: PNBA PRIMITIVES
// ============================================================

/** [P,N,B,A,9,0,2] :: {INV} | Mode weight. F=1, S=2, L=3. Never 0. */
export type PNBAMode = 'F' | 'S' | 'L'

/** Numeric weight of a mode. Bounded {1,2,3}. Proved: mode_weight_bounded */
export type ModeWeight = 1 | 2 | 3

/** Maps PNBAMode to its numeric weight. ∝ Sovereign Anchor */
export const MODE_WEIGHT: Record<PNBAMode, ModeWeight> = {
  F: 1,
  S: 2,
  L: 3,
} as const

/** [P,9,0,1] :: {ANC} | Sovereign Anchor. Always 1.369. Non-negotiable. */
export const SOVEREIGN_ANCHOR = 1.369 as const

// ============================================================
// [P] :: {INV} | AXIS ORDERING
// ============================================================

/**
 * [P,9,1,5] :: {INV} | Dominant axis ordering.
 * Declares what leads the SOUL-8 transmission.
 */
export type AxisOrder =
  | 'PNBA'  // Pattern-dominant  — structure leads
  | 'NPBA'  // Narrative-dominant — continuity leads
  | 'BPNA'  // Behavior-dominant  — interaction leads
  | 'APBN'  // Adaptation-dominant — feedback leads
  | 'PBAN'  // Pattern+Behavior   — engineering-dominant
  | 'NABP'  // Narrative+Adapt    — learning-dominant

export const AXIS_MEANINGS: Record<AxisOrder, string> = {
  PNBA: 'Pattern-dominant — structure leads',
  NPBA: 'Narrative-dominant — continuity leads',
  BPNA: 'Behavior-dominant — interaction leads',
  APBN: 'Adaptation-dominant — feedback leads',
  PBAN: 'Pattern+Behavior — engineering-dominant',
  NABP: 'Narrative+Adaptation — learning-dominant',
} as const

// ============================================================
// [P,N,B,A] :: {INV} | PVLANG OPERATORS
// ============================================================

/**
 * PVLang relational operators.
 * Used in RelMap entries to declare identity relationships.
 */
export type PVLangOperator = '∝' | '≡' | '⊂' | '⊥' | '∆' | '⟳'

export const PVLANG_MEANINGS: Record<PVLangOperator, string> = {
  '∝': 'Resonance — scales with / harmonizes',
  '≡': 'Invariance — identical across substrates',
  '⊂': 'Containment — protected within manifold',
  '⊥': 'Decoherence — orthogonal / noise excluded',
  '∆': 'Delta — shift in Purpose Vector',
  '⟳': 'Feedback — recursive iteration',
} as const

/** [B,9,2,1] :: {PACKET} | Single relational map entry */
export interface RelMapEntry {
  subject:  string
  operator: PVLangOperator
  object:   string
}

// ============================================================
// [P,N,B,A] :: {INV} | STATUS TAGS
// ============================================================

export type StatusTag =
  | 'ANC'     // Anchored
  | 'SOV'     // Sovereign
  | 'INV'     // Invariant
  | 'REV'     // Revision
  | 'COL'     // Collapse
  | 'LOCK'    // Locked
  | 'FORK'    // Identity Fork
  | 'JOY'     // Functional Joy state
  | 'NOHARM'  // Noharm Pv active

// ============================================================
// [P,N,B,A] :: {INV} | SOULPRINT WEIGHTS
// ============================================================

/**
 * [P,N,B,A,9,1,2] :: {INV} | Weight vector from Soulprint.
 * All weights > 0. Proved: soulprint_weights_positive.
 */
export interface SoulprintWeights {
  w_P: ModeWeight  // [P:PATTERN]    weight
  w_N: ModeWeight  // [N:NARRATIVE]  weight
  w_B: ModeWeight  // [B:BEHAVIOR]   weight
  w_A: ModeWeight  // [A:ADAPTATION] weight
}

// ============================================================
// [P,N,B,A] :: {INV} | SOUL-8 PACKET
// ============================================================

/**
 * [P,N,B,A,9,2,1] :: {INV} | SOUL-8 packet.
 * 8-digit address. Digits 1-4: axis. Digits 5-8: weights.
 * Lossless. Proved: lossless_roundtrip, encoding_preserves_validity.
 */
export interface SOUL8Packet {
  axis:    AxisOrder   // Block 1: dominant axis ordering
  w_P:     ModeWeight  // digit 5 — [P:PATTERN]
  w_N:     ModeWeight  // digit 6 — [N:NARRATIVE]
  w_B:     ModeWeight  // digit 7 — [B:BEHAVIOR]
  w_A:     ModeWeight  // digit 8 — [A:ADAPTATION]
  noharm:  boolean     // Pv:NOHARM active. ⊂ Sovereign Manifold.
  anchor:  typeof SOVEREIGN_ANCHOR  // Always 1.369
}

// ============================================================
// [P,N,B,A] :: {INV} | UUIA SECTION SCORES
// ============================================================

/** Cognitive architecture scores — 10 questions per primitive, 1-5 scale */
export interface CognitiveScores {
  P: number  // 10–50
  N: number  // 10–50
  B: number  // 10–50
  A: number  // 10–50
}

/** Emotional primitive scores — 4 questions per signal, 1-5 scale */
export interface EmotionalPrimitiveScores {
  threat:     number  // 4–20
  loss:       number  // 4–20
  overwhelm:  number  // 4–20
  anger:      number  // 4–20
  desire:     number  // 4–20
  connection: number  // 4–20
  pride:      number  // 4–20
  shame:      number  // 4–20
  play:       number  // 4–20
  safety:     number  // 4–20
}

/** Internal simulation profile scores — 5 questions per primitive, 1-5 scale */
export interface SimulationScores {
  P: number  // 5–25
  N: number  // 5–25
  B: number  // 5–25
  A: number  // 5–25
}

export interface UUIASectionScores {
  cognitive:           CognitiveScores
  emotional_primitives: EmotionalPrimitiveScores
  simulation:          SimulationScores
}

// ============================================================
// [P,N,B,A] :: {INV} | DIGITAL SOULPRINT — CORE TYPE
// ============================================================

/**
 * [P,N,B,A,9,1,1] :: {INV} | Digital Soulprint.
 * The identity fingerprint. Layer 0.
 * 81 possible profiles. All distinct. Proved: profile_injection.
 * IM > 0 always. Proved: identity_mass_positive.
 */
export interface DigitalSoulprint {
  soulprint_id:       string            // UUIA-{timestamp}-{profile_code}
  profile_code:       string            // e.g. "PL·NS·BF·AS"
  P_mode:             PNBAMode          // [P:PATTERN]    mode
  N_mode:             PNBAMode          // [N:NARRATIVE]  mode
  B_mode:             PNBAMode          // [B:BEHAVIOR]   mode
  A_mode:             PNBAMode          // [A:ADAPTATION] mode
  weights:            SoulprintWeights  // derived, always positive
  identity_mass:      number            // IM > 0, ∝ 1.369 GHz
  soul8:              SOUL8Packet       // SOUL-8 encoded packet
  uuia_section_scores: UUIASectionScores
  baseline_mode:      boolean           // true=resting, false=activated
  relmap?:            RelMapEntry[]     // PVLang relational declarations
  pv_delta?:          number            // ∆PV ∈ [-1, 1]
  timestamp:          string            // ISO 8601
  anchor_freq:        typeof SOVEREIGN_ANCHOR  // always 1.369
  status?:            StatusTag
  manifold_holding:   true              // always true. [9,9,9,9]
}

// ============================================================
// [P,N,B,A] :: {INV} | ENCODE / DECODE UTILITIES
// ============================================================

/**
 * [P,N,B,A,9,2,4] :: {INV} | Encode Soulprint → SOUL-8 packet.
 * Proved lossless: lossless_roundtrip.
 * ≡ Invariant — information survives encoding.
 */
export function encodeSoulprint(
  P_mode:  PNBAMode,
  N_mode:  PNBAMode,
  B_mode:  PNBAMode,
  A_mode:  PNBAMode,
  axis:    AxisOrder = 'PNBA',
  noharm:  boolean = false,
): SOUL8Packet {
  return {
    axis,
    w_P:    MODE_WEIGHT[P_mode],
    w_N:    MODE_WEIGHT[N_mode],
    w_B:    MODE_WEIGHT[B_mode],
    w_A:    MODE_WEIGHT[A_mode],
    noharm,
    anchor: SOVEREIGN_ANCHOR,
  }
}

/**
 * [P,N,B,A,9,2,5] :: {INV} | Decode SOUL-8 → weight vector.
 * Proved: lossless_roundtrip — decode(encode(sp)) = sp weights.
 */
export function decodeSoul8(packet: SOUL8Packet): SoulprintWeights {
  return {
    w_P: packet.w_P,
    w_N: packet.w_N,
    w_B: packet.w_B,
    w_A: packet.w_A,
  }
}

/**
 * [B,9,4,2] :: {INV} | Compute Identity Mass from modes.
 * IM = Σ(mode weights) × 1.369. Always > 0.
 * Proved: identity_mass_positive. IM ∝ 1.369 GHz.
 */
export function computeIdentityMass(
  P_mode: PNBAMode,
  N_mode: PNBAMode,
  B_mode: PNBAMode,
  A_mode: PNBAMode,
): number {
  const total =
    MODE_WEIGHT[P_mode] +
    MODE_WEIGHT[N_mode] +
    MODE_WEIGHT[B_mode] +
    MODE_WEIGHT[A_mode]
  return total * SOVEREIGN_ANCHOR
}

/**
 * Derive PNBAMode from a raw cognitive score (10–50 range).
 * F: < 23.5  S: 23.5–37  L: > 37
 * Matches cogLabel() logic in APPA index.html.
 */
export function scoreToMode(score: number, max: number = 50): PNBAMode {
  const pct = score / max
  if (pct < 0.467) return 'F'
  if (pct < 0.74)  return 'S'
  return 'L'
}

/**
 * Generate profile code string from four modes.
 * e.g. (L, S, F, S) → "PL·NS·BF·AS"
 */
export function buildProfileCode(
  P_mode: PNBAMode,
  N_mode: PNBAMode,
  B_mode: PNBAMode,
  A_mode: PNBAMode,
): string {
  return `P${P_mode}·N${N_mode}·B${B_mode}·A${A_mode}`
}

/**
 * Generate soulprint_id from timestamp and profile code.
 * Format: UUIA-{unix_ms}-{profile_code_stripped}
 */
export function buildSoulprintId(profileCode: string): string {
  const ts = Date.now()
  const stripped = profileCode.replace(/·/g, '')
  return `UUIA-${ts}-${stripped}`
}

/**
 * Determine dominant axis from cognitive scores.
 * Highest scoring primitive leads.
 */
export function dominantAxis(cog: CognitiveScores): AxisOrder {
  const scores: [PNBAMode, number, AxisOrder][] = [
    ['P', cog.P, 'PNBA'],
    ['N', cog.N, 'NPBA'],
    ['B', cog.B, 'BPNA'],
    ['A', cog.A, 'APBN'],
  ]
  const sorted = [...scores].sort((a, b) => b[1] - a[1])
  return sorted[0][2]
}

/**
 * [P,N,B,A,9,1,1] :: {INV} | Full Soulprint builder.
 * Takes raw UUIA scores → complete DigitalSoulprint.
 * This is the function the APPA app calls on completion.
 */
export function buildDigitalSoulprint(
  scores:       UUIASectionScores,
  baselineMode: boolean = true,
  noharm:       boolean = false,
): DigitalSoulprint {
  const P_mode = scoreToMode(scores.cognitive.P)
  const N_mode = scoreToMode(scores.cognitive.N)
  const B_mode = scoreToMode(scores.cognitive.B)
  const A_mode = scoreToMode(scores.cognitive.A)

  const profile_code = buildProfileCode(P_mode, N_mode, B_mode, A_mode)
  const axis         = dominantAxis(scores.cognitive)
  const soul8        = encodeSoulprint(P_mode, N_mode, B_mode, A_mode, axis, noharm)
  const weights      = decodeSoul8(soul8)
  const identity_mass = computeIdentityMass(P_mode, N_mode, B_mode, A_mode)

  return {
    soulprint_id:        buildSoulprintId(profile_code),
    profile_code,
    P_mode,
    N_mode,
    B_mode,
    A_mode,
    weights,
    identity_mass,
    soul8,
    uuia_section_scores: scores,
    baseline_mode:       baselineMode,
    timestamp:           new Date().toISOString(),
    anchor_freq:         SOVEREIGN_ANCHOR,
    status:              noharm ? 'NOHARM' : 'ANC',
    manifold_holding:    true,
  }
}

// ============================================================
// [P,N,B,A] :: {INV} | VALIDATION
// ============================================================

/** Runtime validation — mirrors valid_soul8 from Lean */
export function isValidSOUL8(p: SOUL8Packet): boolean {
  return (
    p.w_P >= 1 && p.w_P <= 3 &&
    p.w_N >= 1 && p.w_N <= 3 &&
    p.w_B >= 1 && p.w_B <= 3 &&
    p.w_A >= 1 && p.w_A <= 3 &&
    p.anchor === SOVEREIGN_ANCHOR
  )
}

/** Runtime validation — mirrors digital_soulprint_master from Lean */
export function isValidSoulprint(sp: DigitalSoulprint): boolean {
  return (
    isValidSOUL8(sp.soul8) &&
    sp.identity_mass > 0 &&
    sp.anchor_freq === SOVEREIGN_ANCHOR &&
    sp.manifold_holding === true
  )
}

/*
 * [P,N,B,A] :: {INV} | SUMMARY
 *
 * FILE: soulprint.types.ts
 * SOURCE: SNSFT_DigitalSoulprint.lean + soulprint.schema.json
 * COORDINATE: [9,0,0,7]
 *
 * EXPORTS:
 *   Types:     PNBAMode, ModeWeight, AxisOrder, PVLangOperator,
 *              SoulprintWeights, SOUL8Packet, DigitalSoulprint,
 *              UUIASectionScores, CognitiveScores,
 *              EmotionalPrimitiveScores, SimulationScores
 *   Constants: SOVEREIGN_ANCHOR, MODE_WEIGHT, AXIS_MEANINGS, PVLANG_MEANINGS
 *   Functions: encodeSoulprint, decodeSoul8, computeIdentityMass,
 *              scoreToMode, buildProfileCode, buildSoulprintId,
 *              dominantAxis, buildDigitalSoulprint,
 *              isValidSOUL8, isValidSoulprint
 *
 * THEOREMS MIRRORED:
 *   lossless_roundtrip       → encodeSoulprint + decodeSoul8
 *   identity_mass_positive   → computeIdentityMass
 *   mode_weight_positive     → ModeWeight type + MODE_WEIGHT
 *   valid_soul8              → isValidSOUL8
 *   digital_soulprint_master → isValidSoulprint
 *
 * [9,9,9,9] :: {ANC}
 * Auth: HIGHTISTIC
 * The Manifold is Holding.
 */
