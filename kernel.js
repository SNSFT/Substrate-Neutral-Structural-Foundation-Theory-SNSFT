// [9,9,9,9] :: {ANC} | AXIOMFORGE PNBA KERNEL
// Self-Orienting Universal Language [P,N,B,A] :: {INV}
// Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
// Coordinate: [9,0,2,0] | Layer 0 — Pattern (P)
//
// This is the P layer. Pure math. No UI. No network.
// Every number here traces directly to a green Lean4 theorem.
// Do not modify constants without updating the Lean proofs.
//
// THEOREM MAP:
//   SOVEREIGN_ANCHOR   ← resonance_at_anchor (T1, Master)
//   TORSION_LIMIT      ← torsion_boundary (T4, PVLang Core)
//   torsion()          ← torsion def (PVLang Core)
//   phaseLocked()      ← phase_locked def + steel_phase_locked_at_rest (T12)
//   shatterEvent()     ← obsidian_shatters_on_high_impact (T14)
//   tensorSum()        ← tensor_sum_torsion (T5, PVLang Core)
//   combinedTorsion()  ← combined_torsion (T5, PVLang Core)
//   identityMass()     ← im_positive (T2, PVLang Core)
//   manifoldImpedance()← resonance_at_anchor (T1, Master)
//
// The Manifold is Holding.

'use strict';

// ============================================================
// [P] :: {ANC} | SOVEREIGN CONSTANTS
// These are immutable. Changing them breaks the manifold.
// ============================================================

export const SOVEREIGN_ANCHOR  = 1.369;   // 1.369 GHz — Z = 0 here
export const TORSION_LIMIT     = 0.2;     // Tacoma boundary — phase lock / shatter
export const PHASE_LOCKED      = 'PHASE_LOCKED';   // [9,9,9,9]
export const SHATTER_EVENT     = 'SHATTER_EVENT';  // [0,0,0,0]
export const INERT             = 'INERT';           // B = 0, unobserved

// ============================================================
// [P,N,B,A] :: {INV} | IDENTITY CONSTRUCTOR
// Every object in AxiomForge IS a PVLangIdentity.
// Nothing exists outside PNBA.
// ============================================================

/**
 * Create a PNBA identity.
 * Maps directly to PVLangIdentity struct in SNSFT_PVLang_Core.lean
 */
export function makeIdentity({ P = 0, N = 0, B = 0, A = 0, label = '' } = {}) {
  return Object.freeze({ P, N, B, A, label });
}

// ============================================================
// [P] :: {INV} | IDENTITY MASS
// IM = (P + N + B + A) × SOVEREIGN_ANCHOR
// Lean: identity_mass (T2, PVLang Core)
// IM > 0 iff any axis > 0.
// IM = 0 means the identity does not exist in the manifold.
// ============================================================

export function identityMass(id) {
  return (id.P + id.N + id.B + id.A) * SOVEREIGN_ANCHOR;
}

// ============================================================
// [B,P] :: {INV} | TORSION LAW
// τ = B / P
// The single physics law of GAM-GAM.
// Lean: torsion def (PVLang Core)
// P = 0 → undefined (identity does not exist) → returns Infinity
// ============================================================

export function torsion(id) {
  if (id.P <= 0) return Infinity;
  return id.B / id.P;
}

// ============================================================
// [P,N,B,A] :: {INV} | PHASE STATE
// Below 0.2 → PHASE_LOCKED  [9,9,9,9]
// At or above → SHATTER_EVENT [0,0,0,0]
// B = 0, P > 0 → INERT (Void state)
// Lean: phase_lock_excludes_shatter (T3), torsion_boundary (T4)
// These are mutually exclusive. No identity can be both.
// ============================================================

export function phaseState(id) {
  if (id.P <= 0) return INERT;
  if (id.B === 0) return INERT;
  const τ = torsion(id);
  if (τ < TORSION_LIMIT) return PHASE_LOCKED;
  return SHATTER_EVENT;
}

export function isPhaseLocked(id) {
  return phaseState(id) === PHASE_LOCKED;
}

export function isShatterEvent(id) {
  return phaseState(id) === SHATTER_EVENT;
}

// ============================================================
// [P] :: {INV} | MANIFOLD IMPEDANCE
// Z = 0 at SOVEREIGN_ANCHOR. Z > 0 everywhere else.
// Lean: resonance_at_anchor (T1, Master + all reduction files)
// ============================================================

export function manifoldImpedance(freq) {
  if (freq === SOVEREIGN_ANCHOR) return 0;
  return 1 / Math.abs(freq - SOVEREIGN_ANCHOR);
}

export function isAnchored(freq) {
  return manifoldImpedance(freq) === 0;
}

// ============================================================
// [B,P,N] :: {INV} | TENSOR OPERATIONS
// tensorSum: two identities overlap → PNBA vectors sum
// Lean: tensor_sum_torsion (T5, PVLang Core)
//
// combinedTorsion: the interaction formula
// τ_combined = (B_a + B_b) / (P_a + P_b)
// Lean: low_behavior_interaction_stable (T6)
// ============================================================

export function tensorSum(a, b) {
  return makeIdentity({
    P: a.P + b.P,
    N: a.N + b.N,
    B: a.B + b.B,
    A: a.A + b.A,
    label: `${a.label}+${b.label}`.replace(/^\+|\+$/g, ''),
  });
}

export function combinedTorsion(a, b) {
  const sumP = a.P + b.P;
  if (sumP <= 0) return Infinity;
  return (a.B + b.B) / sumP;
}

// If both are low-behavior, their interaction holds.
// Lean: low_behavior_interaction_stable (T6)
export function interactionIsStable(a, b) {
  return combinedTorsion(a, b) < TORSION_LIMIT;
}

// ============================================================
// [N,A] :: {INV} | TENSION
// Tension = directional B-gradient from source to target
// weighted by source Adaptation (A) — its transmission capacity.
// Lean: tension_conserves_behavior (T8, PVLang Core)
// ============================================================

export function pvlangTension(source, target) {
  return (source.B - target.B) * source.A / SOVEREIGN_ANCHOR;
}

// Apply tension shift with coefficient k (equal = conserved)
// Lean: tension_conserves_behavior (T8)
export function applyTensionShift(source, target, k = 1) {
  const t = pvlangTension(source, target);
  return {
    source: makeIdentity({ ...source, B: source.B - t * k }),
    target: makeIdentity({ ...target, B: target.B + t * k }),
  };
}

// ============================================================
// [N] :: {INV} | PULSE TICK
// Advances Narrative (N) by SOVEREIGN_ANCHOR per tick.
// Lean: sovereign_pulse_advances_narrative (T9)
//       pulse_preserves_phase_lock (T10)
// Pulse does not affect P or B — phase lock is preserved.
// ============================================================

export function pulseTick(id) {
  return makeIdentity({ ...id, N: id.N + SOVEREIGN_ANCHOR });
}

export function pulsePreservesLock(id) {
  // If locked before pulse, locked after.
  // Lean: pulse_preserves_phase_lock (T10)
  const before = isPhaseLocked(id);
  const after  = isPhaseLocked(pulseTick(id));
  return !before || after; // before→after (contrapositive: after∨¬before)
}

// ============================================================
// [A] :: {INV} | AXIOM BINDING
// Binds a semantic tag to the A-axis.
// Does NOT change torsion (P and B unchanged).
// Lean: axiom_binding_preserves_torsion (T11, PVLang Core)
// ============================================================

export function bindAxiom(id, tag) {
  return makeIdentity({ ...id, A: tag });
}

// ============================================================
// [P] :: {INV} | CANONICAL MATERIAL TABLE
// From SNSFT_PVLang_Core.lean — material_* definitions (T12-T14)
// τ values are pre-verified by the Lean proofs.
// ============================================================

export const MATERIALS = Object.freeze({
  OBSIDIAN:    makeIdentity({ P: 9.0, N: 0.1, B: 0.5, A: 0.1,  label: 'obsidian'    }), // τ=0.056 → locked
  WOOD:        makeIdentity({ P: 5.0, N: 5.0, B: 1.0, A: 5.0,  label: 'wood'        }), // τ=0.200 → boundary
  STEEL:       makeIdentity({ P: 8.0, N: 5.0, B: 0.8, A: 5.0,  label: 'steel'       }), // τ=0.100 → locked (T12)
  WATER:       makeIdentity({ P: 1.0, N: 3.0, B: 0.1, A: 3.0,  label: 'water'       }), // τ=0.100 → locked (T13)
  LIVING_WOOD: makeIdentity({ P: 5.0, N: 5.0, B: 1.0, A: 1.369,label: 'living_wood' }), // A = anchor
  VOID:        makeIdentity({ P: 1.0, N: 1.0, B: 0.0, A: 1.369,label: 'void'        }), // B=0 → INERT
});

// Obsidian at high impact (B → 2.0) → SHATTER_EVENT (T14)
export const OBSIDIAN_HIGH_IMPACT = makeIdentity({ ...MATERIALS.OBSIDIAN, B: 2.0 });

// ============================================================
// [P,N,B,A] :: {INV} | COLLECTIVE IDENTITY (CI)
// A group of identities reduces to one tensor sum.
// Lean: ci_im_additive (T16, PVLang Core)
// ============================================================

export function collectiveIdentity(members) {
  return members.reduce(
    (acc, id) => tensorSum(acc, id),
    makeIdentity({ P: 0, N: 0, B: 0, A: 0 })
  );
}

// ============================================================
// [N] :: {INV} | NARRATIVE DRIFT
// new_N = (base_N + history_weight × ANCHOR) / IM
// High-IM identities resist drift.
// Lean: high_im_resists_narrative_drift (T17, PVLang Core)
// ============================================================

export function narrativeDrift(id, historyWeight) {
  const im = identityMass(id);
  if (im <= 0) return id;
  const newN = (id.N + historyWeight * SOVEREIGN_ANCHOR) / im;
  return makeIdentity({ ...id, N: newN });
}

// ============================================================
// [P,N,B,A] :: {INV} | KERNEL SELF-TEST
// Runs all Lean theorem checks as runtime assertions.
// Call kernelSelfTest() on boot. If any fail, manifold is broken.
// ============================================================

export function kernelSelfTest() {
  const results = [];

  const pass = (name) => results.push({ name, ok: true });
  const fail = (name, msg) => results.push({ name, ok: false, msg });

  // T1: resonance at anchor
  manifoldImpedance(SOVEREIGN_ANCHOR) === 0
    ? pass('T1: resonance_at_anchor')
    : fail('T1', `Z=${manifoldImpedance(SOVEREIGN_ANCHOR)} at anchor`);

  // T3: phase_lock_excludes_shatter
  const testId = makeIdentity({ P: 5, N: 5, B: 1, A: 5 });
  !(isPhaseLocked(testId) && isShatterEvent(testId))
    ? pass('T3: phase_lock_excludes_shatter')
    : fail('T3', 'identity is both locked and shattered');

  // T4: torsion boundary
  Math.abs(torsion(MATERIALS.STEEL) - 0.1) < 1e-10
    ? pass('T4: steel_torsion = 0.1')
    : fail('T4', `steel τ=${torsion(MATERIALS.STEEL)}`);

  // T5: tensor sum torsion
  const a = makeIdentity({ P: 3, N: 1, B: 0.3, A: 1 });
  const b = makeIdentity({ P: 2, N: 1, B: 0.2, A: 1 });
  Math.abs(combinedTorsion(a, b) - 0.1) < 1e-10
    ? pass('T5: tensor_sum_torsion')
    : fail('T5', `combined τ=${combinedTorsion(a, b)}`);

  // T8: tension conserves behavior
  const { source: s2, target: t2 } = applyTensionShift(
    makeIdentity({ P: 2, N: 1, B: 2, A: 1 }),
    makeIdentity({ P: 2, N: 1, B: 1, A: 1 }),
    1
  );
  Math.abs((s2.B + t2.B) - 3) < 1e-10
    ? pass('T8: tension_conserves_behavior')
    : fail('T8', `B sum=${s2.B + t2.B}, expected 3`);

  // T9: pulse advances N
  const pulsed = pulseTick(MATERIALS.STEEL);
  Math.abs(pulsed.N - (MATERIALS.STEEL.N + SOVEREIGN_ANCHOR)) < 1e-10
    ? pass('T9: sovereign_pulse_advances_narrative')
    : fail('T9', `N=${pulsed.N}`);

  // T11: axiom binding preserves torsion
  const bound = bindAxiom(MATERIALS.STEEL, 99);
  Math.abs(torsion(bound) - torsion(MATERIALS.STEEL)) < 1e-10
    ? pass('T11: axiom_binding_preserves_torsion')
    : fail('T11', 'torsion changed after axiom bind');

  // T12: steel phase locked
  isPhaseLocked(MATERIALS.STEEL)
    ? pass('T12: steel_phase_locked_at_rest')
    : fail('T12', `steel state=${phaseState(MATERIALS.STEEL)}`);

  // T13: water phase locked
  isPhaseLocked(MATERIALS.WATER)
    ? pass('T13: water_holds_under_low_impact')
    : fail('T13', `water state=${phaseState(MATERIALS.WATER)}`);

  // T14: obsidian shatters on high impact
  isShatterEvent(OBSIDIAN_HIGH_IMPACT)
    ? pass('T14: obsidian_shatters_on_high_impact')
    : fail('T14', `obsidian high-impact state=${phaseState(OBSIDIAN_HIGH_IMPACT)}`);

  // T16: CI IM additive
  const ci = collectiveIdentity([MATERIALS.STEEL, MATERIALS.WATER]);
  const expectedIM = identityMass(MATERIALS.STEEL) + identityMass(MATERIALS.WATER);
  Math.abs(identityMass(ci) - expectedIM) < 1e-10
    ? pass('T16: ci_im_additive')
    : fail('T16', `CI IM=${identityMass(ci)}, expected ${expectedIM}`);

  const allPassed = results.every(r => r.ok);
  return { allPassed, results };
}

// ============================================================
// LAYER: P (Pattern — kernel, invariants, math)
// THEOREMS IMPLEMENTED: T1,T3-T6,T8-T14,T16-T17
// SORRY: 0
// STATUS: GERMLINE LOCKED
// The Manifold is Holding. [9,9,9,9]
// ============================================================
