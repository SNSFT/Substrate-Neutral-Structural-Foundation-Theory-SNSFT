# SNSFT Sovereign Drive Simulator
## Identity Physics Engine · v2.0
**Live:** uuia.app/sovereigndrive · **Architect:** HIGHTISTIC · **Anchor:** 1.369 GHz
**Status:** GERMLINE LOCKED · **Corpus:** DOI 10.5281/zenodo.18719748 · **0 sorry**

---

## What This Is

A real-time 3D identity physics simulator. Load any PNBA state — a phase state, a periodic element, a molecular compound, or an exotic resonance entity from the corpus — and watch the sovereign manifold render it. The sim computes τ, IM, Pv, IVA output, and IMS gate status live, visualizing the dynamic equation:

```
d/dt(IM · Pv) = Σ λ_X · O_X · S + F_ext
```

This is not a particle physics simulator. It does not model physical appearance. It renders PNBA identity states — what each entity looks like in the manifold. Different structure, same equation.

---

## The Four Categories

Every preset belongs to one of four categories. Each renders with a different 3D geometry and color palette so you know immediately what class of thing you're looking at.

| Category | Geometry | Faces | Color | What it contains |
| :--- | :--- | :---: | :--- | :--- |
| **PHASE STATES** | Dodecahedron | 12 | Cyan | Noble, Locked, IVA, Shatter — the four fundamental states |
| **ELEMENTS** | Octahedron | 8 | Green | Periodic table elements from locked Slater corpus values |
| **BIOFUSE** | Icosahedron | 20 | Light green | Molecular compounds — harmonic reduction of bonded atoms |
| **EREs** | Tetrahedron | 4 | Gold | Exotic Resonance Entities from corpus leans |

The geometry choice is structural. Dodecahedron = 12 faces = digital soulprint (APPA). Octahedron = 8 faces = atomic orbital symmetry. Icosahedron = 20 faces = biological complexity. Tetrahedron = 4 faces = minimal quantum structure.

---

## The Physics Engine

### Core Variables

```
P = Pattern    — structural capacity (Slater Z_eff for elements, corpus value for EREs)
N = Narrative  — shell depth / period / continuity thread
B = Behavior   — open bonds / unpaired electrons / coupling output
A = Adaptation — ionization energy / anchor feedback

τ = B / P                          torsion
TL = ANCHOR / 10 = 0.1369          torsion limit (emergent, not chosen)
IM = (P + N + B + A) × 1.369       Identity Mass
Pv = purpose vector                evolves via dynamic equation
```

### Phase States (classify function — fixed in v2.0)

```
τ = 0           → NOBLE    zero torsion, ground state, maximum potential
0 < τ < TL      → LOCKED   phase-locked, stable, below threshold
τ ≈ TL (±0.5%)  → IVA      sovereign flow state, peak drive corridor
τ ≥ TL          → SHATTER  pattern genesis, torsion exceeded
```

**v2.0 fix:** The IVA branch was unreachable in v1.0 — the SHATTER check caught `τ ≥ TL` before the IVA check could fire. Fixed by checking `τ < TL` explicitly before returning IVA.

### Dynamic Equation

```
drive = A × P × B × IMS_gate
dvdt  = (drive − F_ext) / IM
Pv   += dvdt × dt
```

IMS gate = 1 when anchor-locked, 0 when drifted. If the IMS gate is off, Pv never builds — the purpose vector collapses to zero. Not by rule. By physics.

### IVA Output

```
Δv_sovereign = √IM × (1 + g_r) × ln((P + A) / B)
Δv_classical = √IM × ln((P + A) / B)
IVA gain     = Δv_sovereign / Δv_classical = (1 + g_r)
```

The sovereign gain `(1 + g_r)` is only available when anchor-locked. IMS gate off → gain = 1 → classical output only.

---

## Preset Library

### Phase States
| Preset | P | B | τ | State | Note |
| :--- | :---: | :---: | :---: | :--- | :--- |
| NOBLE | 2.000 | 0.000 | 0.0000 | NOBLE | Zero torsion · ground state |
| LOCKED | 1.500 | 0.100 | 0.0667 | LOCKED | Phase-locked below TL |
| IVA PEAK | 1.500 | 0.205 | 0.1367 | IVA | τ≈TL · flow state · max drive |
| SHATTER | 1.000 | 0.500 | 0.5000 | SHATTER | τ>>TL · pattern genesis |

### Elements (Locked Slater Corpus Values)
| Element | P | B | τ | IM | State | Note |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| H | 1.000 | 1.0 | 1.0000 | 24.09 | SHATTER | 1 open bond |
| He | 1.700 | 0.0 | 0.0000 | 38.73 | NOBLE | Noble gas · highest IE |
| C | 3.250 | 4.0 | 1.2308 | 30.82 | SHATTER | 4 open bonds · life scaffold |
| O | 4.550 | 2.0 | 0.4396 | 33.09 | SHATTER | 2 unpaired |
| Ne | 5.850 | 0.0 | 0.0000 | 43.00 | NOBLE | Noble gas · high IM |
| Si | 2.250 | 4.0 | 1.7778 | 27.93 | SHATTER | Semiconductor |
| Fe | 3.750 | 4.0 | 1.0667 | 32.38 | SHATTER | 4 unpaired d-electrons · Fe-56 peak |
| Zn | 4.200 | 0.0 | 0.0000 | 29.56 | NOBLE | d10 filled · first Noble transition metal |
| Au | 5.850 | 1.0 | 0.1709 | 38.44 | SHATTER | 1 open s-bond · near-locked |
| U | 4.800 | 4.0 | 0.8333 | 39.69 | SHATTER | 4 open f-bonds · actinide |

### BioFuse (Molecular Compounds)
| Compound | P | B | τ | IM | State | Note |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| H₂O | 0.4505 | 0.0 | 0.0000 | 30.21 | NOBLE | All bonds satisfied · life solvent · T2 |
| CO₂ | 1.3382 | 0.0 | 0.0000 | 36.91 | NOBLE | C fully bonded · carbon cycle |
| NH₃ | 0.3071 | 0.0 | 0.0000 | 34.00 | NOBLE | Amino acid precursor |
| Fe-O | 2.0557 | 2.0 | 0.9729 | 40.63 | SHATTER | GAM Collider k=2 · Fe 2 bonds remaining · reversible O₂ coupling |

P values for BioFuse computed via harmonic reduction: `P_mol = harmonic(P_atoms)`. B=0 when all bonds satisfied. Fe-O retains B=2 — GAM Collider k=2 result (O consumes 2 of Fe's 4 bonds, leaving B=2).

**Collision sweep note:** At k=3, Fe+O reaches Noble (B_out=0, τ=0) — the fully saturated state where all bonds are consumed. The heme-specific k=2 leaves Fe with 2 remaining bonds, giving τ=0.9729 deep SHATTER. This is the reversible coupling zone — stable enough to bind O₂, unstable enough to release it. The biology follows from the PNBA arithmetic.

**Pending lean:** `SNSFL_FeO_Heme.lean [9,0,8,5]` — Fe+O GAM Collider reduction. Will formally prove k=2 heme coupling, τ=0.9729, the k=3 Noble emergence (fully saturated state), and the τ monotonic decrease invariant `dτ/dk = -2/P_out`. All inputs from proved corpus constants. Candidacy: SNSFL.

**The Noble-SHATTER-SHATTER pattern:** H₂O (Noble), C (Shatter), Fe (Shatter). The three components of carbon-based life sit at exactly three different phase states. Proved formally in `SNSFL_BiologicalAnalog.lean [9,0,8,4]` T15. Load all three sequentially and compare the geometries.

### EREs — Exotic Resonance Entities
| Entity | P | B | τ | IM | State | Coordinate |
| :--- | :---: | :---: | :---: | :---: | :--- | :--- |
| Soverium | 0.9878 | 0.000 | 0.0000 | 4.09 | NOBLE | [9,9,1,46] |
| Lumium | 0.9878 | 0.007 | 0.0074 | 10.16 | LOCKED | [9,9,1,53] |
| Zoivum | 1.3690 | 0.094 | 0.0684 | 18.43 | LOCKED | [9,9,1,56] |
| Higgs | 0.5080 | 0.000 | 0.0000 | 4.71 | NOBLE | [9,9,4,5] |
| W⁺ boson | 0.5200 | 0.052 | 0.1000 | 9.68 | LOCKED | [9,9,4,6] |
| Z⁰ boson | 0.5900 | 0.059 | 0.1000 | 9.79 | LOCKED | [9,9,4,7] |
| Ξcc⁺ | 1.3590 | 0.000 | 0.0000 | 6.13 | NOBLE | [9,9,2,33] |
| Toponium tt̄ | 0.7000 | 0.000 | 0.0000 | 9.33 | NOBLE | [9,9,2,34] |
| Coherent state | 0.6845 | 0.000 | 0.0000 | 20.10 | NOBLE | [9,9,1,57] |
| Dirac fermion | 0.0005 | 1.000 | 1834.9 | 4.13 | SHATTER | — |

**Notes on specific EREs:**

**Soverium** — the quantum vacuum ground state. B=0, τ=0, Noble. With A=0, the IVA drive term is zero — Pv never builds. This is structurally correct: the vacuum has no adaptation axis. The sim will run in a perfectly inert Noble state.

**Lumium** — the photon field. B=1/α=0.00730. Deep LOCKED at τ=0.0074. The photon is massless but not Noble — it has coupling (B>0) but extremely low torsion. High A=4.423 gives strong adaptation. IVA output is significant.

**Zoivum** — the life operator from `[9,9,1,56]`. LOCKED at τ=0.068, operating at 50% of TL. High A=13.69 (ANCHOR/TL) means massive IVA potential. This is the highest sustained IVA output of any preset — run it and watch Pv climb.

**W/Z bosons** — both LOCKED at τ=0.100. They sit just below TL — the weak force carriers operate near the IVA corridor. High A=2.5 gives strong drive. Note that τ≈TL*0.73 — closer to threshold than any element.

**Ξcc⁺ and Toponium** — both Noble (B=0, τ=0). Two recently confirmed exotic baryons that reduce to Noble ground states. The cc diquark in Ξcc⁺ is the PNBA expression of the Nobel-prize-predicted doubly-charmed baryon confirmed at LHCb 2026.

**Dirac fermion (free electron)** — τ=1835. Deep SHATTER. P=0.000545 (electron mass in Planck units), B=1 (one free fermionic mode). This is not a bug — a free unbound electron is genuinely at extreme torsion. The sim caps the torsion display to prevent overflow but logs the actual value.

---

## 3D Scene Elements

**Core mesh** — geometry changes by category. Pulses at 1.369 Hz (`sin(t × ANCHOR × π × 2)`). Rotation rate scales with τ — higher torsion = faster spin. Color shifts toward SHATTER red or NOBLE purple as state changes.

**Anchor ring** — torus at radius 1.369. Always present. Pulses with the anchor frequency. Color tinted by current category.

**TL ring** — smaller torus at `TL × 8 = 1.097` radius. Glows brighter as τ approaches TL — shows proximity to the IVA corridor.

**Field lines** — 24 CatmullRom curves radiating outward. Colored by category. Opacity scales with Pv and IMS gate. Off when IMS gate = 0.

**PNBA shells** — four concentric wireframe spheres, one per axis. Scale proportional to current axis value. Opacity scales with axis value. Each rotates independently.

**Torsion cone** — appears when τ > 0. Scales with τ/TL. Purple at low τ, orange near TL, red at SHATTER.

**IVA thrust plume** — appears when Pv > 0.1 and IMS gate active. Scale proportional to Pv × (1 + g_r).

**Particles** — 200 points orbiting in PNBA-driven paths. Speed scales with IM × IMS gate. Colored by category. Size scales with Pv.

---

## Controls

**Drag** — orbit camera. **Scroll** — zoom in/out (range 2–20 units).

**PNBA sliders** — P (0.0001–10), N (0.5–14), B (0–5), A (0–15). Ranges expanded from v1 to accommodate ERE values like Zoivum A=13.69.

**F_EXT** — external force opposing the drive term. Increases resistance in the dynamic equation.

**IVA gain g_r** — scales sovereign output: `Δv_sov = Δv_classical × (1 + g_r)`.

**Anchor Lock** — IMS gate toggle. Off: Pv collapses to zero, field lines go dark. The physics enforces this — not a rule.

**RUN / STOP / RESET** — simulation controls. RUN activates the physics loop. RESET clears all counters and Pv.

**Sim Speed** — 1 (slow) to 10 (max). Adjusts the physics update interval.

---

## Event Log

The event log records every phase transition with timestamp, state, τ, IM, and Pv. Transitions are color-coded by state. Loading a preset logs the full preset description including corpus coordinate. The log holds up to 100 entries before cycling.

---

## Bottom Bar Stats

| Stat | What it tracks |
| :--- | :--- |
| CYCLES | Total physics update iterations |
| NOBLE EVENTS | Number of τ=0 transitions |
| SHATTER EVENTS | Number of τ≥TL crossings |
| IVA PEAKS | Number of IVA corridor entries |
| MAX Pv | Peak purpose vector achieved |
| MAX IVA Δv | Peak sovereign drive output |
| LOADED | Current preset name, colored by category |

---

## What Changed in v2.0

- `classify()` bug fixed — IVA state is now reachable
- 4-category system — PHASE / ELEMENT / BIOFUSE / ERE
- Geometry swaps by category — dodecahedron / octahedron / icosahedron / tetrahedron
- Color palette swaps by category — cyan / green / light green / gold
- 24 presets (up from 12) with verified corpus values
- Category badge and HUD overlay showing corpus coordinate
- Slider ranges expanded to accommodate full element and ERE value ranges
- Dirac fermion τ display capped to prevent overflow (actual value logged)
- BioFuse compounds: H₂O, CO₂, NH₃, Fe-O
- EREs added: Soverium, Lumium, Zoivum, Higgs, W/Z bosons, Ξcc⁺, Toponium, coherent state

---

## Collider Discoveries — Pending Leans

Three things emerged from running the GAM Collider during v2.0 development that aren't yet in the corpus:

**[9,0,8,5] SNSFL_FeO_Heme.lean — Fe+O coupling**
Fe (SHATTER, τ=1.067) + O (SHATTER, τ=0.440) at k=2 gives τ=0.9729, deep SHATTER. At k=3 the result collapses to Noble (τ=0, B_out=0) — the fully saturated heme state. The τ monotonic decrease invariant holds across the full sweep: each increment of k reduces τ by exactly 2/P_out. All inputs from proved corpus constants Fe [9,9,1,26] and O [9,9,1,8].

**[9,9,1,x] Noble Gas Series Completion**
He, Ne, Ar, Zn, Kr, Xe — all B=0, all Noble, all provable from the same rule: filled subshells → B=0 → τ=0 → NOBLE. This pattern is implicit across the atomic series but never stated as a single master theorem. One file, one conjunct: `∀ element with filled valence shell, B=0 ∧ τ=0 ∧ NOBLE`.

**Noble Emergence from SHATTER Collision**
The k=3 Fe+O result is structurally significant on its own: two SHATTER inputs at the right coupling constant collapse to Noble. This is pattern genesis in reverse — not SHATTER emerging from Noble (which is the conventional direction), but Noble emerging from controlled SHATTER coupling. May warrant its own theorem in the BiologicalAnalog or FeO lean.

---


Live:        uuia.app/sovereigndrive
File:        sds3d.html
Version:     v2.0
Corpus:      DOI 10.5281/zenodo.18719748
Depends on:  SNSFL_BiologicalAnalog.lean  [9,0,8,4]
             SNSFT_Quantum_Node_Forge.lean [9,9,3,3]
             gamcollider.html (locked Slater corpus)
Sorry:       0
Status:      GERMLINE LOCKED

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
Soldotna, Alaska. March 2026.
```
