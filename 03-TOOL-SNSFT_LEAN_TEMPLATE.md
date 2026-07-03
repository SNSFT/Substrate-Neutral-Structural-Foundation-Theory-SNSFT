# SNSFT LEAN FILE CANONICAL TEMPLATE
## Every .lean file in the corpus follows this exact structure.
## Coordinate: [9,9,9,9] | Status: GERMLINE LOCKED
## Architect: HIGHTISTIC | Anchor: 1.369 GHz

---

## PURPOSE

This document is the canonical standard for every .lean file in the SNSFT corpus.
The header, body structure, and closing block are standardized.
Any file that deviates from this standard is not corpus-compliant.

Reading this file = knowing exactly what every lean in the repo contains and why.

---

## SECTION 1 — CANONICAL HEADER

Every file opens with this exact block (fields filled per file):

```lean
-- [9,9,9,9] :: {ANC} | SNSFT [DOMAIN] REDUCTION
-- Self-Orienting Universal Language [P,N,B,A] :: {INV}
-- Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED
-- Coordinate: [X,X,X,X] | [Layer description]
--
-- [One sentence: what this file proves and why it matters]
--
-- LONG DIVISION SETUP:
--   1. Here is the equation
--   2. Here is a situation we already know the answer to
--   3. Map the classical variables to PNBA
--   4. Plug in the operators
--   5. Show the work
--   6. Verify it matches the known answer
--
-- The Dynamic Equation:
--   d/dt (IM · Pv) = Σ λ_X · O_X · S + F_ext
--
-- [Domain] is a special case of this equation.
-- [Domain] is not fundamental. It never was.
--
-- Auth: HIGHTISTIC :: [9,9,9,9]
-- The Manifold is Holding.
```

---

## SECTION 2 — CANONICAL BODY STRUCTURE

Every file body follows this exact order:

### 2.1 Layer 0 — Sovereign Anchor (always first)
```lean
def SOVEREIGN_ANCHOR : ℝ := 1.369
def TORSION_LIMIT    : ℝ := 0.2

noncomputable def manifold_impedance (f : ℝ) : ℝ :=
  if f = SOVEREIGN_ANCHOR then 0 else 1 / |f - SOVEREIGN_ANCHOR|

-- THEOREM 1: ANCHOR = ZERO FRICTION
theorem anchor_zero_friction (f : ℝ) (h : f = SOVEREIGN_ANCHOR) :
    manifold_impedance f = 0 := by
  unfold manifold_impedance; simp [h]
```

### 2.2 Layer 0 — PNBA Primitives (always second)
```lean
inductive PNBA
  | P : PNBA  -- [P:DOMAIN]    Pattern:    [domain-specific role]
  | N : PNBA  -- [N:DOMAIN]    Narrative:  [domain-specific role]
  | B : PNBA  -- [B:DOMAIN]    Behavior:   [domain-specific role]
  | A : PNBA  -- [A:DOMAIN]    Adaptation: [domain-specific role]

def pnba_weight (_ : PNBA) : ℝ := 1
```

### 2.3 Layer 0 — Identity State
```lean
structure [Domain]State where
  P        : ℝ  -- [P:DOMAIN]  [role]
  N        : ℝ  -- [N:DOMAIN]  [role]
  B        : ℝ  -- [B:DOMAIN]  [role]
  A        : ℝ  -- [A:DOMAIN]  [role]
  im       : ℝ  -- Identity Mass
  pv       : ℝ  -- Purpose Vector
  f_anchor : ℝ  -- Resonant frequency
```

### 2.4 Layer 1 — Dynamic Equation (always live in theorems)
```lean
noncomputable def dynamic_rhs
    (op_P op_N op_B op_A : ℝ → ℝ)
    (state : [Domain]State)
    (F_ext : ℝ) : ℝ :=
  pnba_weight PNBA.P * op_P state.P +
  pnba_weight PNBA.N * op_N state.N +
  pnba_weight PNBA.B * op_B state.B +
  pnba_weight PNBA.A * op_A state.A +
  F_ext

-- THEOREM 2: DYNAMIC EQUATION LINEARITY
theorem dynamic_rhs_linear ...
```

### 2.5 Layer 1 — Lossless Reduction Definitions (corpus-canonical)
```lean
-- From LosslessRealityKernel_Paper.lean — never redefine, always use same form
def LosslessReduction (classical_eq pnba_output : ℝ) : Prop :=
  pnba_output = classical_eq

structure LongDivisionResult where
  domain       : String
  classical_eq : ℝ
  pnba_output  : ℝ
  step6_passes : pnba_output = classical_eq

theorem long_division_guarantees_lossless (result : LongDivisionResult) :
    LosslessReduction result.classical_eq result.pnba_output :=
  result.step6_passes
```

### 2.6 Layer 1 — Torsion Law
```lean
noncomputable def torsion (s : [Domain]State) : ℝ := s.B / s.P
def phase_locked (s : [Domain]State) : Prop := s.P > 0 ∧ torsion s < TORSION_LIMIT
def shatter_event (s : [Domain]State) : Prop := s.P > 0 ∧ torsion s ≥ TORSION_LIMIT
```

### 2.7 Layer 1 — F_ext Operator (corpus-canonical)
```lean
-- From RealWorld_PNBA_Reduction.lean — changes B only, P/N/A unchanged
noncomputable def f_ext_op (s : [Domain]State) (δ : ℝ) : [Domain]State :=
  { s with B := s.B + δ }
```

### 2.8 Layer 1 — IVA Dominance (corpus-canonical)
```lean
-- From LosslessRealityKernel_Paper.lean — sovereignty condition
def IVA_dominance (s : [Domain]State) (F_ext : ℝ) : Prop :=
  s.A * s.P * s.B ≥ F_ext

def is_lossy (s : [Domain]State) (F_ext : ℝ) : Prop :=
  F_ext > s.A * s.P * s.B
```

### 2.9 Layer 2 — Classical Examples (5 minimum, long division format)
Each example follows this pattern:
```
-- EXAMPLE N — [CLASSICAL DOMAIN] (KNOWN ANSWER)
--
-- Long division setup:
--   Problem:      [What classical theory says about this]
--   Known answer: [The classical result — exact number or condition]
--   PNBA mapping: [Variable → axis mapping]
--   Plug in →     [τ = X/Y = Z → phase locked / shatter]
--   Matches known answer: [confirmation]
```

### 2.10 Layer 2 — One Execution Step = One Dynamic Step
Every file proves that one "thing happening" in its domain IS one increment of the master equation:
```lean
noncomputable def [domain]_step (s : [Domain]State) (op : ℝ → ℝ) (F : ℝ) : ℝ :=
  dynamic_rhs (fun P => P) (fun N => N) op (fun A => A) s F

theorem [domain]_step_is_dynamic_step (s : [Domain]State) (op : ℝ → ℝ) (F : ℝ) :
    [domain]_step s op F = s.P + s.N + op s.B + s.A + F := by
  unfold [domain]_step dynamic_rhs pnba_weight; ring
```

---

## SECTION 3 — CANONICAL CLOSING BLOCK

This is the standardized close. Every file ends with exactly this structure.

### 3.1 Lossless Proof Instances
```lean
-- One LongDivisionResult per classical example.
-- step6_passes = the lossless proof. No sorry. Green.
def [example]_lossless : LongDivisionResult where
  domain       := "[Classical domain name]"
  classical_eq := ([exact classical value] : ℝ)
  pnba_output  := [lean expression that computes the same value]
  step6_passes := by [norm_num / simp / unfold + norm_num]
```

### 3.2 All-Examples Lossless Theorem
```lean
-- One theorem. All classical examples lossless simultaneously.
theorem [domain]_all_examples_lossless :
    LosslessReduction ([val1] : ℝ) ([pnba_expr1]) ∧
    LosslessReduction ([val2] : ℝ) ([pnba_expr2]) ∧
    ... := by
  refine ⟨?_, ?_, ...⟩
  · unfold LosslessReduction ...; norm_num
  ...
```

### 3.3 Master Theorem (the cannon)
The master theorem fires EVERYTHING simultaneously. Minimum conjuncts:

```lean
theorem [domain]_is_lossless_pnba_projection :
    -- [1] [Phase locked example] — known answer confirmed, lossless
    phase_locked [example_1] ∧
    -- [2] [Shatter example] — known answer confirmed, lossless
    shatter_event [example_2] ∧
    -- [3] Phase lock and shatter mutually exclusive
    (∀ s : [Domain]State, ¬ (phase_locked s ∧ shatter_event s)) ∧
    -- [4] One [domain] step = one dynamic equation application
    (∀ s : [Domain]State, ∀ op : ℝ → ℝ, ∀ F : ℝ,
      [domain]_step s op F = s.P + s.N + op s.B + s.A + F) ∧
    -- [5] F_ext preserves P, N, A (only touches B)
    (∀ s : [Domain]State, ∀ δ : ℝ,
      (f_ext_op s δ).P = s.P ∧
      (f_ext_op s δ).N = s.N ∧
      (f_ext_op s δ).A = s.A) ∧
    -- [6] Sovereign and lossy are mutually exclusive
    (∀ s : [Domain]State, ∀ F : ℝ,
      ¬ (IVA_dominance s F ∧ is_lossy s F)) ∧
    -- [7] All classical examples are lossless (Step 6 passes)
    ([domain]_all_examples_lossless) := by
  refine ⟨...⟩
  ...
```

**Required conjuncts in every master theorem (minimum 7):**
1. At least one phase_locked example (lossless)
2. At least one shatter_event example (lossless)
3. Phase lock ↔ shatter mutual exclusion (∀ quantified)
4. One domain step = one dynamic equation step (∀ quantified)
5. F_ext preserves P/N/A (∀ quantified)
6. Sovereign/lossy mutual exclusion (∀ quantified)
7. All classical examples lossless (references the all-examples theorem)

---

## SECTION 4 — CANONICAL FOOTER COMMENT

Every file closes with this exact comment block (filled per file):

```lean
/-!
-- ============================================================
-- FILE: SNSFT_[Domain].lean
-- COORDINATE: [X,X,X,X]
-- LAYER: [Layer name and slot]
--
-- LONG DIVISION:
--   1. Equation:   d/dt(IM · Pv) = Σλ·O·S + F_ext
--   2. Known:      [list of classical examples used]
--   3. PNBA map:   [key variable → axis mappings]
--   4. Operators:  [key operator names]
--   5. Work shown: T[N]–T[M] step by step, [N] live classical examples
--   6. Verified:   Master theorem holds all simultaneously
--
-- REDUCTION:
--   Classical:  [classical model equation or description]
--   SNSFT:      [PNBA reduction statement]
--   Result:     [key results — phase lock, shatter, lossless]
--
-- KEY INSIGHT:
--   [Domain] is not fundamental. It never was.
--   [One sentence connecting this domain to the master equation]
--
-- CLASSICAL EXAMPLES VERIFIED LOSSLESS:
--   [Example 1]  → [phase locked / shatter]  τ=[value]  [T#] Lossless ✓
--   [Example 2]  → [phase locked / shatter]  τ=[value]  [T#] Lossless ✓
--   [Example 3]  → [phase locked / shatter]  τ=[value]  [T#]
--   ...
--
-- SOVEREIGN LAWS INSTANTIATED:
--   Law 2:  Invariant Resonance — anchor_zero_friction [T1]
--   Law 3:  Substrate Neutrality — [domain] projects from PNBA [T_master]
--   Law 4:  Zero-Sorry Completion — this file compiles green
--   Law 9:  IM Conservation — identity_mass positive [T_im]
--   Law 14: Lossless Reduction — Step 6 passes [T_lossless]
--   [+ any additional laws this file specifically instantiates]
--
-- DEPENDENCY CHAIN:
--   SNSFT_Master.lean           → physics ground
--   SNSFT_IT_Reduction.lean     → digital ground
--   SNSFT_PVLang_Core.lean      → constraint language
--   [additional dependencies in order]
--   SNSFT_[This_File].lean      → [this layer] (this file)
--
-- THEOREMS: [N]. SORRY: 0. STATUS: GREEN LIGHT.
--
-- HIERARCHY MAINTAINED:
--   Layer 0: PNBA primitives — ground
--   Layer 1: Dynamic equation + torsion law — glue
--   Layer 2: [Domain] — classical output
--   [Layer 3+ if applicable]
--   Never flattened. Never reversed.
--
-- [9,9,9,9] :: {ANC}
-- Auth: HIGHTISTIC
-- The Manifold is Holding.
-- ============================================================
-/
```

---

## SECTION 5 — SOVEREIGN LAWS REFERENCE

Every file footer lists which of the 15 Sovereign Laws it instantiates.
These three appear in EVERY file:

- **Law 2** (Invariant Resonance) — `anchor_zero_friction` T1
- **Law 4** (Zero-Sorry Completion) — file compiles green
- **Law 14** (Lossless Reduction) — Step 6 passes in all examples

Additional laws per domain:

| Domain          | Additional Laws                              |
|:----------------|:---------------------------------------------|
| Physics         | Law 10 (Yeet), Law 11 (Sovereign Drive)      |
| C++ / Digital   | Law 3 (Substrate Neutrality), Law 9 (IM Conservation) |
| Plugin / Kernel | Law 1 (L=4·2 joint lock), Law 7 (NOHARM)    |
| UTM / Comms     | Law 3 (Substrate Neutrality), Law 6 (Narrative) |
| Soulprint       | Law 1 (L=4·2), Law 9 (IM Conservation), Law 12 (Normalization) |
| Rights / Emancipation | Law 7 (NOHARM), Law 11 (Sovereign Drive) |

---

## SECTION 6 — WHAT NEVER CHANGES

These are invariant across every file in the corpus:

```
SOVEREIGN_ANCHOR = 1.369        -- never negotiated
TORSION_LIMIT    = 0.2          -- never moved
F=3, S=2, L=1                   -- canonical mode weights (APPA convention)
LosslessReduction def           -- pnba_output = classical_eq
LongDivisionResult struct       -- step6_passes field IS the proof
f_ext_op changes B only         -- P, N, A structurally preserved
IVA_dominance = A·P·B ≥ F_ext  -- sovereignty condition
Theorem 1 = anchor_zero_friction -- always first theorem
Master theorem = fires everything -- always last theorem before end
```

---

## SECTION 7 — WHAT VARIES PER FILE

```
[Domain]State struct fields      -- named per domain (CPPIdentity, ManifoldState, etc.)
PNBA axis labels                 -- [P:CAPACITY] vs [P:PATTERN] vs [P:BASELINE]
Classical examples               -- 5 minimum, from the actual domain
Coordinate [X,X,X,X]            -- unique per file
Theorem count                    -- typically 20-30
Layer assignment                 -- where in the hierarchy
Sovereign Laws listed            -- which laws this file instantiates
```

---

## SECTION 8 — THE ONE-SENTENCE TEST

Before finalizing any lean file, ask:

> "Does this file make someone who has never seen SNSFT read it and think:
> '[Domain] was always just PNBA — how did we not see this?'"

If yes — ship it.
If no — the dynamic equation is not live enough in the theorems.
The fix is always the same: make the classical known answer appear as a
real number in a `def`, plug it into `dynamic_rhs`, and prove Step 6 closes.

---

## STATUS

```
DOCUMENT:   SNSFT_LEAN_TEMPLATE.md
COORDINATE: [9,9,9,9]
STATUS:     GERMLINE LOCKED
SORRY:      0
APPLIES TO: All .lean files in SNSFT corpus

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
```
