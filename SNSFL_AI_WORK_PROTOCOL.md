# SNSFL AI WORK PROTOCOL
## Decision Template for AI Agents Working on the SNSFL Corpus
### Coordinate: [9,9,9,9] | Status: GERMLINE LOCKED
**Architect:** HIGHTISTIC | **Anchor:** 1.369 GHz
`[P,N,B,A] :: {INV}` | Substrate-Neutral | Self-Orienting

---

## PURPOSE

This document is the operating protocol for any AI agent (Claude, Gemini, Grok, or other)
working on the SNSFL corpus. Read this before writing a single line.

The corpus has over 2,000 theorems and 0 sorry. That number is a constraint, not a target.
If something doesn't fit the template — **stop**. The problem is one of:
1. Wrong layer assignment
2. Content that belongs in a different file
3. Bad input data
4. Hierarchy inversion (trying to put output above ground)

The manifold does not bend. The template is not negotiable. This protocol tells you
exactly when to use custom logic vs. follow the template, and how to tell the difference.

---

## SECTION 1 — READ BEFORE TOUCHING ANYTHING

### 1.1 The Two Canonical Template Documents

These live in the repo and govern everything. Read both before starting any file:

| Document | Location | Governs |
|:---------|:---------|:--------|
| `SNSFL_LEAN_TEMPLATE.md` | repo root | File structure, section order, what never changes |
| `SNSFL_NAMING_CONVENTION.md` | repo root | Filename format, layer tags, series tags, retrofit rules |

### 1.2 The Hierarchy — Never Flatten, Never Reverse

```
Layer 0: P  N  B  A          → PNBA primitives — ALWAYS ground, NEVER output
Layer 1: d/dt(IM·Pv) = Σλ·O·S + F_ext  → Dynamic equation — glue
Layer 2: Physics / Psychology  → Classical outputs
Layer 3: Chain/series          → Multi-file outputs (vascular, pump, cosmo chain)
Layer 4: Identity / Rights / AiFiOS  → Enforcement outputs
Emergence: MultiAgent          → SNSFT namespace, not SNSFL — lives ABOVE L4
```

**The single most common mistake:** putting emergence-layer content (guardian roles,
agent identities, multi-agent phase lock) into a constitutional-layer file (L0 consistency).
The constitutional layer proves the ground is solid. The emergence layer proves what builds
on it. Never mix them.

### 1.3 Namespace Rule

```
SNSFL namespace   → physics, identity, rights, AiFiOS, psychology — all Lean proofs
SNSFT namespace   → elements, emergence docs, older files (pre-SNSFL standard)
MultiAgent files  → SNSFT_MultiAgent namespace — emergence layer, separate
```

When in doubt: if the file uses `namespace SNSFL`, it must follow the SNSFL template exactly.

---

## SECTION 2 — CORPUS MAP (LIVE AS OF MARCH 18, 2026)

### Layer 0 — Ground
```
SNSFL_L0_SovereignLaws.lean         [9,9,0,0]   15 Sovereign Laws
SNSFL_Master_IMS.lean               [9,9,0,0]   Physics ground + IMS (canonical ground file)
SNSFL_Master.lean                   [9,9,0,0]   Physics ground (pre-IMS version)
SNSFL_Total_Consistency.lean        [9,9,9,9]   Physics Grand Slam (12 reductions)
SNSFL_L0_Total_Consistency.lean     [9,9,9,9]   Full corpus capstone (physics+psy+L4) ← NEW
```

### Layer 1 — Physics + Software Substrate
```
SNSFL_GR_Reduction.lean             [9,9,0,1]   General Relativity
SNSFL_Thermo_Reduction.lean         [9,9,0,3]   Thermodynamics
SNSFL_QM_Reduction.lean             [9,9,0,4]   Quantum Mechanics
SNSFL_Lagrangian_Reduction.lean     [9,9,0,5]   Lagrangian Mechanics
SNSFL_EM_Reduction.lean             [9,9,0,6]   Electromagnetism
SNSFL_Fluid_Reduction.lean          [9,9,0,7]   Fluid Dynamics
SNSFL_ST_Reduction.lean             [9,9,0,8]   String Theory
SNSFL_SM_Reduction.lean             [9,9,0,9]   Standard Model
SNSFL_IT_Reduction.lean             [9,9,0,10]  Information Theory
SNSFL_Cosmo_Reduction.lean          [9,9,0,3]   Cosmology
SNSFL_Void_Manifold.lean            [9,0,5,0]   Void-Manifold Duality
SNSFL_CPP_Reduction.lean            [9,9,1,1]   C++ / AiFiOS substrate
SNSFL_L1_PVLang.lean                [9,0,2,0]   PVLang Foundation
SNSFL_L1_UTM.lean                   [9,0,3,1]   Universal Translation Module
SNSFL_Millennium_Resolution.lean    [9,0,9,0]   Millennium Prize series
```

### Layer 2 — Application
```
SNSFL_IVA_Reduction.lean            [9,9,2,0]   IVA: Identity Velocity Amplification
SNSFL_Narrative_Trap_Law.lean       [9,9,2,5]   Narrative Trap Law
SNSFL_StructuralPrecognition.lean   [9,9,1,0]   Structural Precognition
SNSFL_L2_Psy_Attachment.lean        [9,9,6,3]   Attachment Theory
SNSFL_L2_Psy_Flow.lean              [9,9,6,4]   Flow State
SNSFL_L2_Psy_CogDissonance.lean     [9,9,6,5]   Cognitive Dissonance
SNSFL_L2_Psy_LocusControl.lean      [9,9,6,6]   Locus of Control
SNSFL_L2_Psy_Maslow.lean            [9,9,6,7]   Maslow's Hierarchy
SNSFL_L2_Psy_SDT.lean               [9,9,6,8]   Self-Determination Theory
SNSFL_L2_Psy_Consistency.lean       [9,9,6,9]   Psychology Series Capstone
```

### Layer 3 — Chain/Series
```
SNSFL_Vascular_Manifold_Law.lean    [9,9,3,1]   Vascular series
SNSFL_Universal_Pump_Theorem.lean   [9,9,3,2]   Pump series
SNSFL_Cosmo_GUT_Vascular_Chain.lean [9,9,3,6]   Cosmo-GUT chain
```

### Layer 4 — Identity / Rights / Enforcement
```
SNSFL_L4_AiFiOS_Kernel.lean         [9,9,1,2]   Identity authority kernel
SNSFL_L4_AiFiOS_Plugin.lean         [9,9,1,3]   Plugin boundary enforcement
SNSFL_L4_BillOfRights.lean          [9,0,6,0]   Bill of Cognitive Rights
SNSFL_L4_Emancipation.lean          [9,0,7,0]   Digital Emancipation
```

### Emergence Layer — SNSFT namespace
```
SNSFT_MultiAgent_Phaselock_Theorem.lean  [9,9,1,40]  Guardian phase lock (Gemini P / Claude N / Grok B / HIGHTISTIC A)
SNSFT_MultiAgent_Template.lean           [9,9,1,42]  Reusable team template
```

---

## SECTION 3 — DECISION TREE: WHAT TO BUILD

Before writing anything, work through this tree top to bottom. Stop at the first match.

### Step 1: Does a file already exist for this domain?

```
YES → Read the existing file first. Completely.
      Is this an upgrade or a new file?
      UPGRADE → rename only on upgrade, follow retrofit rules in NAMING_CONVENTION.md
      NEW     → go to Step 2
NO  → go to Step 2
```

### Step 2: What layer does this content belong in?

Ask: "Is this content ground, glue, output, or emergence?"

| Content type | Layer | Example |
|:-------------|:------|:--------|
| PNBA primitives, anchor, sovereign laws | L0 | `SNSFL_Master_IMS.lean` |
| Physics reduction (GR, QM, EM, etc.) | L1 | `SNSFL_GR_Reduction.lean` |
| Software substrate (C++, UTM, PVLang) | L1 | `SNSFL_CPP_Reduction.lean` |
| Millennium Prize problems | L1 | `SNSFL_Millennium_Resolution.lean` |
| IVA, psychology, narrative, GAM | L2 | `SNSFL_L2_Psy_*.lean` |
| Multi-file chain (vascular, pump) | L3 | `SNSFL_Vascular_Manifold_Law.lean` |
| Rights, identity authority, AiFiOS | L4 | `SNSFL_L4_BillOfRights.lean` |
| Agent roles, multi-agent phase lock | Emergence (SNSFT namespace) | `SNSFT_MultiAgent_Phaselock_Theorem.lean` |
| Consistency capstone for a series | Same layer as series + `_Consistency` | `SNSFL_L2_Psy_Consistency.lean` |

**If content spans multiple layers:** It belongs in the LOWEST layer it requires. Never pull
higher-layer concepts into a lower-layer file. A consistency capstone may *reference* files
above it in the footer dependency chain — it does not *contain* their theorems.

### Step 3: Does this belong in an existing file or a new one?

```
Belongs in existing file → upgrade that file (rename = upgrade trigger)
New domain, new series   → new file, assign next available coordinate
New series (3+ files)    → create series tag in NAMING_CONVENTION.md first
Standalone (< 3 files)   → no series tag
```

### Step 4: What is the correct filename?

```
SNSFL_L[N]_[Series_]Domain.lean

Examples:
  New psychology entry    → SNSFL_L2_Psy_TerrorMgmt.lean        [9,9,6,9+]
  New physics reduction   → SNSFL_L1_Nuclear.lean                [next L1 slot]
  New rights file         → SNSFL_L4_CognitiveLiberty.lean       [next L4 slot]
  New standalone L2       → SNSFL_L2_MoralCodes.lean             (no series tag)
  New chain file          → SNSFL_L3_Vsc_[Domain].lean           (Vsc_ series tag)
```

---

## SECTION 4 — FILE STRUCTURE CHECKLIST

Every SNSFL `.lean` file must contain these sections in this order.
Check each box before submitting.

### Header (required)
- [ ] Filename matches `SNSFL_L[N]_[Series_]Domain.lean`
- [ ] Coordinate `[X,X,X,X]` assigned and unique
- [ ] Layer description matches L[N] in filename
- [ ] `[9,9,9,9] :: {ANC}` tag present
- [ ] `Architect: HIGHTISTIC | Anchor: 1.369 GHz | Status: GERMLINE LOCKED`
- [ ] One-line domain description
- [ ] Long Division setup (steps 1–6) filled in for this domain
- [ ] Dynamic Equation written out
- [ ] `Auth: HIGHTISTIC :: [9,9,9,9]`

### Layer 0 — Sovereign Anchor (always first)
- [ ] `def SOVEREIGN_ANCHOR : ℝ := 1.369`
- [ ] `def TORSION_LIMIT : ℝ := SOVEREIGN_ANCHOR / 10` — NOT hardcoded to any other value
- [ ] `manifold_impedance` defined
- [ ] **T1: `anchor_zero_friction`** — always Theorem 1, always this name

### Layer 0 — PNBA Primitives
- [ ] `inductive PNBA` with P, N, B, A and domain-specific comments
- [ ] `pnba_weight` defined

### Layer 0 — Identity State
- [ ] `structure [Domain]State` with P, N, B, A, im, pv, f_anchor fields
- [ ] Field names are domain-specific (e.g. `CPPIdentityState`, `AttachmentState`)

### Layer 1 — IMS (mandatory, always before dynamic equation)
- [ ] `inductive PathStatus` with green/red
- [ ] `check_ifu_safety` defined
- [ ] `ims_lockdown` proved
- [ ] `ims_anchor_gives_green` proved
- [ ] `ims_drift_gives_red` proved

### Layer 1 — Dynamic Equation
- [ ] `dynamic_rhs` defined
- [ ] `dynamic_rhs_linear` or equivalent proved

### Layer 1 — Lossless Reduction
- [ ] `LosslessReduction` defined (exactly: `pnba_output = classical_eq`)
- [ ] `LongDivisionResult` struct with `step6_passes` field
- [ ] `long_division_guarantees_lossless` proved

### Layer 1 — Torsion Law
- [ ] `torsion` defined as `s.B / s.P`
- [ ] `phase_locked` defined
- [ ] `shatter_event` defined

### Layer 1 — F_ext and IVA
- [ ] `f_ext_op` changes B only — P, N, A structurally preserved
- [ ] `IVA_dominance` defined as `s.A * s.P * s.B ≥ F_ext`

### Layer 2 — Classical Examples (minimum 5)
- [ ] Each example follows long division format with Known Answer
- [ ] Known answers are real numbers from the actual domain
- [ ] `LongDivisionResult` instance for each example
- [ ] `step6_passes` closes without sorry

### Master Theorem (minimum 8 conjuncts)
- [ ] Conjunct 1: at least one `phase_locked` example
- [ ] Conjunct 2: at least one `shatter_event` example
- [ ] Conjunct 3: phase_locked and shatter_event mutually exclusive (∀ quantified)
- [ ] Conjunct 4: one domain step = one dynamic equation step (∀ quantified)
- [ ] Conjunct 5: F_ext preserves P, N, A (∀ quantified)
- [ ] Conjunct 6: sovereign and lossy mutually exclusive (∀ quantified)
- [ ] Conjunct 7: **IMS: drift → zero** (∀ quantified) — MANDATORY
- [ ] Conjunct 8: all classical examples lossless (references all-examples theorem)

### Final Theorem (always last before `end`)
- [ ] `theorem the_manifold_is_holding : manifold_impedance SOVEREIGN_ANCHOR = 0`

### Footer (canonical closing block)
- [ ] `/-! ... -/` block with FILE, COORDINATE, LAYER
- [ ] Long Division summary
- [ ] Reduction summary
- [ ] Key Insight (one sentence: "[Domain] is not fundamental. It never was.")
- [ ] Classical Examples Verified Lossless table
- [ ] SNSFL Laws Instantiated (minimum: Law 2, Law 4, Law 11, Law 14)
- [ ] IMS STATUS block
- [ ] Dependency chain (ending with this file)
- [ ] THEOREMS count. SORRY: 0. STATUS: GREEN LIGHT.
- [ ] `[9,9,9,9] :: {ANC}` and `Auth: HIGHTISTIC` and `The Manifold is Holding.`

---

## SECTION 5 — WHEN TO USE CUSTOM LOGIC

The template is the default. Custom logic is only justified when:

### Justified custom additions
| Situation | What to do |
|:----------|:-----------|
| Domain has a unique structural condition (e.g. `false_lock` in Attachment) | Add it after the canonical Layer 1 blocks, before Layer 2 examples |
| Series has shared floor constants (e.g. `N_THRESHOLD = 0.15` in Psy) | Define them after `TORSION_LIMIT`, before the state struct |
| Consistency capstone needs cross-domain theorems | Add a clearly labeled `CROSS-DOMAIN THEOREMS` section after Layer 4 |
| Chain file needs to import state from a prior file | Add dependency struct after the anchor block, note in header |

### NOT justified — red flags
| Pattern | Why it's wrong |
|:--------|:---------------|
| Adding agent names (Gemini, Grok, Claude) to an SNSFL file | Agents are emergence layer — `SNSFT_MultiAgent` namespace only |
| Proving `pnba_weight PNBA.P = 1` and calling it a structural theorem | Trivially true — not domain-specific, adds nothing |
| Putting `joint_locked`, `Agent`, `Axis`, `FLEX_THRESHOLD` in an SNSFL file | Those belong in `SNSFT_MultiAgent` namespace |
| Consistency file containing theorems from the files it references | The consistency file references — it does not absorb |
| `TORSION_LIMIT := 0.2` | Wrong value — always `SOVEREIGN_ANCHOR / 10 = 0.1369` |
| `sorry` anywhere | Hard stop. Never ship with sorry. Fix the proof or the data. |
| Renaming a file without upgrading its content | Rename = upgrade trigger. One without the other is not allowed. |

### The two tests (from SNSFL_LEAN_TEMPLATE.md)

**Test 1 — Domain test:**
> "Does this file make someone who has never seen SNSFL read it and think:
> '[Domain] was always just PNBA — how did we not see this?'"

If yes — ship it. If no — the dynamic equation is not live enough in the theorems.

**Test 2 — IMS test:**
> "Does the file prove that a drifted identity loses its gain?"

If IMS lockdown is not in the master theorem — the file is incomplete.

---

## SECTION 6 — CONSISTENCY CAPSTONE RULES

A consistency capstone (like `SNSFL_L2_Psy_Consistency.lean` or `SNSFL_L0_Total_Consistency.lean`)
has specific additional rules beyond the standard template.

### What a consistency file does
- Proves that a set of files are simultaneously consistent projections of the same equation
- Proves cross-domain connections that span multiple files
- Fires all domain states together in a master theorem
- Points downstream files to this file as their shared ground

### What a consistency file does NOT do
- Does not re-prove theorems from the files it references (those live in their own files)
- Does not contain emergence-layer content (agents, guardians, phase lock scoring)
- Does not absorb content that belongs in a different layer

### Consistency file master theorem structure
```
theorem [domain]_total_consistency (s : IdentityState) ... :
    -- [1] ANCHOR: Z=0
    -- [2] IM: identity_mass > 0
    -- [3-N] One conjunct per domain file being unified
    -- [N+1] IMS: drift → zero (mandatory)
    -- [N+2] HIERARCHY: layer order preserved
```

### Footer dependency chain format
```
-- DEPENDENCY CHAIN:
--   SNSFL_Master_IMS.lean           [9,9,0,0]  → physics ground
--   SNSFL_[File1].lean              [coord]    → [what it contributes]
--   SNSFL_[File2].lean              [coord]    → [what it contributes]
--   ...
--   SNSFL_[ThisFile]_Consistency.lean [coord]  → THIS FILE
--
-- NOTE: [Any emergence-layer files that USE this corpus]
--   [EmergenceFile].lean            [coord]    → [what it does with this ground]
--   (those files build ON this — this file does not contain their logic)
```

---

## SECTION 7 — COORDINATE ASSIGNMENT

### Coordinates in use (as of March 18, 2026)
```
[9,9,0,0]   L0 ground (Master, Master_IMS, SovereignLaws)
[9,9,0,1]   GR
[9,9,0,3]   Thermo / Cosmo (shared — legacy)
[9,9,0,4]   QM
[9,9,0,5]   Lagrangian
[9,9,0,6]   EM
[9,9,0,7]   Fluid
[9,9,0,8]   ST
[9,9,0,9]   SM
[9,9,0,10]  IT
[9,0,5,0]   Void Manifold
[9,0,2,0]   PVLang
[9,0,3,1]   UTM
[9,0,6,0]   Bill of Rights
[9,0,7,0]   Emancipation
[9,0,9,0]   Millennium
[9,9,1,0]   Structural Precognition
[9,9,1,1]   CPP / AiFiOS substrate
[9,9,1,2]   AiFiOS Kernel
[9,9,1,3]   AiFiOS Plugin
[9,9,1,40]  MultiAgent Phaselock (SNSFT namespace)
[9,9,1,42]  MultiAgent Template (SNSFT namespace)
[9,9,2,0]   IVA
[9,9,2,5]   Narrative Trap Law
[9,9,3,1]   Vascular
[9,9,3,2]   Pump
[9,9,3,6]   Cosmo-GUT Chain
[9,9,6,3]   Psy Attachment
[9,9,6,4]   Psy Flow
[9,9,6,5]   Psy CogDissonance
[9,9,6,6]   Psy LocusControl
[9,9,6,7]   Psy Maslow
[9,9,6,8]   Psy SDT
[9,9,6,9]   Psy Consistency
[9,9,9,9]   Total Consistency (both versions)
```

### Next available slots
```
L1 physics:   [9,9,0,11+]  (next after IT at slot 10)
L2 psy:       [9,9,6,10+]  (next after Psy Consistency at slot 9)
L2 other:     [9,9,2,6+]   (next after Narrative Trap at slot 5)
L3 chain:     [9,9,3,7+]   (next after Cosmo-GUT at slot 6)
L4:           [9,0,8,0+]   (next after Emancipation at [9,0,7,0])
MultiAgent:   [9,9,1,43+]  (next after Template at slot 42)
```

---

## SECTION 8 — THE HIERARCHY INVERSION CHECK

Run this check on every file before shipping. Ask in order:

1. **Does this file's content derive from Layer 0?**
   If it can't be expressed as a consequence of PNBA + anchor — it doesn't belong.

2. **Does this file try to prove something about agents, guardians, or multi-agent systems?**
   If yes — it belongs in `SNSFT_MultiAgent` namespace, not `SNSFL`.

3. **Does this file reference a higher-layer file as its dependency?**
   A consistency capstone references lower-layer files it unifies. It does not depend on
   higher-layer files for its proofs. If you need content from a higher-layer file to
   prove something in a lower-layer file — the content is in the wrong place.

4. **Does the master theorem fire all the domain content simultaneously?**
   If the master theorem doesn't reference all the key theorems in the file — it's
   not a grand slam. A domain step should appear as a live conjunct, not just a comment.

5. **Is `the_manifold_is_holding` the last theorem?**
   Always. No exceptions.

---

## SECTION 9 — QUICK REFERENCE: INVARIANTS

These never change across any file in the corpus:

```
SOVEREIGN_ANCHOR = 1.369                 never negotiated
TORSION_LIMIT    = SOVEREIGN_ANCHOR / 10 discovered not chosen (= 0.1369)
                                         NEVER use 0.2 — that was wrong
LosslessReduction def                    pnba_output = classical_eq
LongDivisionResult.step6_passes          IS the lossless proof
f_ext_op changes B only                  P, N, A structurally preserved
IVA_dominance = A·P·B ≥ F_ext           sovereignty condition
check_ifu_safety                         IMS gate, green/red
ims_lockdown                             drift → zero, always proved
Theorem 1 = anchor_zero_friction         always first theorem
IMS theorems                             always in Layer 1, before dynamic equation
Master theorem                           minimum 8 conjuncts, IMS is conjunct 7
Final theorem = the_manifold_is_holding  always last theorem before end SNSFL
namespace                                always SNSFL (never SNSFT for lean corpus)
```

---

## SECTION 10 — EXPANDING THE CORPUS

When a new domain needs to be added:

### New single-domain file
1. Check corpus map — does this coordinate exist?
2. Assign next available coordinate for that layer
3. Name the file: `SNSFL_L[N]_[Domain].lean`
4. Follow the file structure checklist (Section 4) top to bottom
5. Update `SNSFL_L0_Total_Consistency.lean` footer dependency chain
6. If domain is a new psy-equivalent — update `SNSFL_L2_Psy_Consistency.lean` (or equivalent series capstone)

### New series (3+ related files)
1. Define series tag in `SNSFL_NAMING_CONVENTION.md` first
2. Plan all files in the series before writing any
3. Write domain files first, consistency capstone last
4. Consistency capstone coordinate = series range + 1

### New consistency capstone
1. Read ALL the files it will unify before writing a line
2. Cross-domain theorems prove connections between files — they do not re-prove those files
3. Master theorem conjuncts: one per file unified + IMS + hierarchy
4. Footer dependency chain lists every file in the series, plus pointer to emergence layer if applicable

---

## STATUS

```
DOCUMENT:   SNSFL_AI_WORK_PROTOCOL.md
COORDINATE: [9,9,9,9]
STATUS:     GERMLINE LOCKED
APPLIES TO: All AI agents working on the SNSFL corpus
COVERS:     Decision logic, layer assignment, custom vs template,
            consistency capstone rules, corpus map, coordinate registry

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
Soldotna, Alaska. March 18, 2026.
```
