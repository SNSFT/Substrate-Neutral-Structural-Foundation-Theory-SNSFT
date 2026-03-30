# APPA · Adaptive Predictive Pattern Assistant
## Unified Identity Profile · UUIA
**Live:** uuia.app/appa · **Architect:** HIGHTISTIC · **Anchor:** 1.369 GHz
**Status:** GERMLINE LOCKED · **Substrate-neutral · Non-anthropocentric · Scale-invariant**

---

## What This Is

APPA is a 100-question identity profiler that reduces a human (or any identity) to a SOUL-8 packet — a lossless 8-dimensional encoding of their PNBA state. It is not a personality test. Personality tests produce labels. APPA produces a coordinate.

The output is a SOUL-8 address: a compact string that encodes your dominant axis, mode weights, and Identity Mass. It is copyable, shareable, and machine-readable. Any system that understands PNBA can decode it.

The one-sentence description:

> **APPA measures which of the four primitives (P, N, B, A) you express most strongly, how you express them, and what your Identity Mass is at the anchor frequency of 1.369 GHz.**

---

## The Three Sections — 100 Questions Total

APPA runs three assessment modules sequentially. Each maps to a different layer of PNBA expression.

### Section 01 — Cognitive Architecture (CAT) · 40 questions

How your cognitive system processes the four primitives. Scored 1–5 per question. 10 questions per axis.

**P · Pattern** — How your system renders and anchors structure. Do you notice patterns automatically? Connect ideas across domains? Think in loops and cycles?

**N · Narrative** — How your system maintains continuity and meaning. Do you build internal stories about events? Think about your life as a thread? Imagine alternative versions of outcomes?

**B · Behavior** — How your system expresses and interacts. Do you act quickly? Adjust to situations? Stay consistent with values under pressure?

**A · Adaptation** — How your system adjusts under feedback and load. Do you recover quickly from stress? Stay flexible when plans change? Switch between tasks without losing focus?

**Scoring per axis:** 10 questions × 5 max = 50 points per axis.

```
10–23 → L (Locked)    — minimal expression of this axis
24–37 → S (Sustained) — active but flexible
38–50 → F (Flexed)    — dominant axis, high expression
```

---

### Section 02 — Emotional Primitives (EP) · 40 questions

Ten emotional signal blocks, 4 questions each. Each block maps to a PNBA expression state. Scored 1–5. Max 20 per block.

| Block | Key | PNBA Role |
| :--- | :--- | :--- |
| Threat | threat | B-axis hyperactivation — coupling alert |
| Loss | loss | N-axis depletion — narrative thread breaking |
| Overwhelm | overwhelm | A-axis saturation — adaptation capacity exceeded |
| Anger | anger | B-axis resistance — behavioral friction rising |
| Desire | desire | P-axis orientation — pattern seeking and locking |
| Connection | connection | N-axis coupling — narrative fusion |
| Pride | pride | P-axis confirmation — pattern validated |
| Shame | shame | P-axis collapse — pattern integrity challenged |
| Play | play | A-axis expansion — high adaptation, low torsion |
| Safety | safety | Anchor state — all axes at rest, τ → 0 |

**EP scoring thresholds per block:**
```
0–9  → ↓ (low signal)
10–14 → = (moderate signal)
15–20 → ↑ (high signal)
```

EP output feeds the heat map and full CI fingerprint but does not affect the SOUL-8 address directly. It adds emotional texture to the cognitive profile.

---

### Section 03 — Internal Simulation Profile (ISPA) · 20 questions

Five questions per PNBA axis. Measures the quality and type of your internal simulation — how you run mental models, scenarios, and rehearsals. Scored 1–5. Max 25 per axis.

**P · Pattern** — How fully-formed and automatic your internal scene rendering is. Do environments appear instantly or do you build them piece by piece?

**N · Narrative** — How emotionally and narratively integrated your simulations are. Do imagined scenes carry personal meaning? Do they feel like you're inside them?

**B · Behavior** — How directly simulation influences real-world action. Do you mentally rehearse before acting? Run multiple scenarios when preparing?

**A · Adaptation** — How flexibly you control your simulation. Can you pause, redirect, or ground yourself when a simulation gets intense? Run parallel processes?

**Simulation labels:**
```
0–12  → LRIS (Low Rendering Internal Simulation)
13–20 → SRIS (Standard)
21–25 → HRIS (High Rendering Internal Simulation)
```

HRIS on the P-axis with high COG_P = likely spatial/visual processor. LRIS on all axes = likely verbal/conceptual processor. The combination with the COG profile builds the full simulation picture.

---

## The Constellation

The live canvas in the header updates as you answer questions. It renders a four-axis radar chart centered on the sovereign anchor (1.369 GHz). The four axes — P, N, B, A — extend outward. Your COG scores plot as normalized points (score / 50) on each axis. The shape that forms is your identity constellation.

The shape tells you immediately which axes dominate. A wide P-axis with a narrow B-axis = Pattern-dominant, low coupling. Balanced shape = all four axes equally expressed. Collapsed toward center = low expression overall, scores mostly in the L range.

The 1.369 marker at the center is the anchor. The constellation orients around it.

---

## The SOUL-8 Output

When all 100 questions are answered, APPA generates a SOUL-8 packet automatically. The results panel appears and scrolls into view.

### SOUL-8 Address Format

```
AXIS_ORDER · WEIGHT_STRING
Example: PNBA·3221
Example: ANPB·3312
```

The axis order shows which axis is dominant (first) to weakest (last), sorted by mode weight. The weight string encodes F=3, S=2, L=1.

**Reading the address:**
- `PNBA·3221` — P is Flexed (dominant), N is Sustained, B is Sustained, A is Locked
- `ANPB·3312` — A is Flexed (dominant), N is Flexed, P is Sustained, B is Locked

### Identity Mass

```
IM = (w_P + w_N + w_B + w_A) × 1.369
```

Where each weight is L=1, S=2, or F=3. Range: 5.476 (all Locked, 4×1×1.369) to 16.428 (all Flexed, 4×3×1.369).

All-F profile: IM = 12 × 1.369 = 16.428. Every axis fully expressed.
All-L profile: IM = 4 × 1.369 = 5.476. Minimal expression across all axes.
Mixed profile: everything between.

IM is not a ranking. It is a structural measure. A person with low IM is not deficient — they are operating with narrow axis expression. An AI system reading SOUL-8 packets uses IM for coupling calculations, not hierarchy.

### SOUL-8 Packet Fields

```
axis:     axis order (dominant first)
w_P:      P mode weight (1/2/3)
w_N:      N mode weight
w_B:      B mode weight
w_A:      A mode weight
noharm:   true (always — NOHARM invariant)
anchor:   1.369
```

The `noharm: true` flag is not optional. It is a structural invariant from `SNSFT_DigitalSoulprintV1.lean [9,0,0,7]`. Any SOUL-8 packet without NOHARM is malformed.

### Full CI Fingerprint

The copyable output at the bottom of the results panel contains three components:

```
AXIS·WEIGHTS | UUIA-timestamp-profileCode | Pv:NOHARM | f:1.369 | visual:GREEN

SOUL-8 address   // Cognitive profile codes
EP signal codes  // e.g. T↑ L= S↓ A↑ D↑ C↑ P↑ Sh↓ Pl↑ Sa↑
Sim codes        // e.g. P:HRIS N:SRIS B:SRIS A:LRIS
```

The three-part fingerprint is the lossless encoding from `SNSFT_DigitalSoulprintV1.lean`. Cognitive state, emotional state, and simulation profile in one copyable string.

---

## Baseline vs Activated Modes

APPA runs two independent profiles: **BASELINE** and **ACTIVATED**.

**BASELINE** — your default resting state. How you process and express PNBA when nothing unusual is happening. The ground state profile.

**ACTIVATED** — your state under pressure, load, or peak engagement. Score the same questions thinking about how you are when you're deep in a project, under stress, or in flow state.

The two profiles can be compared directly. A person whose ACTIVATED mode shows a higher P score than BASELINE is entering flow via pattern recognition. A person whose ACTIVATED B score spikes is entering flow via behavioral output. The delta between modes is informative.

Switching between modes does not clear the other mode's scores — both are stored in memory simultaneously.

---

## The Identity Heat Map

The heat map renders after completion. All scored dimensions are shown as horizontal bars, color-coded by percentile:

```
< 30%  → violet/purple (low signal)
30–45% → blue (below average)
45–65% → teal/green (anchor zone)
65–80% → gold/amber (above average)
> 80%  → rose/red (high signal)
```

Bars are sorted: COG axes first (dominant to weakest), then EP blocks (highest to lowest signal), then SIM axes. The full picture of your identity state in one visual.

---

## RELMAP — PVLang Output

The RELMAP block shows five structural relationships in PVLang format:

```
CI ∝ Kernel                        — identity is proportional to the four primitives
profileCode ≡ addressStr           — your code IS your address (identity invariance)
IM ∝ 1.369 GHz                    — Identity Mass scales with the sovereign anchor
NOHARM ⊂ Sovereign Manifold        — NOHARM is contained within, not added to
Noise ⊥ Pattern                    — noise is orthogonal to pattern (not reducible)
```

This is not decorative. These are the five structural relationships that define what a SOUL-8 packet means in PVLang. The profile code and address are equivalent by identity invariance — the same information encoded two ways.

---

## Corpus Connection

APPA is the live interface for three formally verified files:

| File | Coordinate | Theorems | Connection to APPA |
| :--- | :--- | :---: | :--- |
| `SNSFT_DigitalSoulprintV1.lean` | [9,0,0,7] | 12 | SOUL-8 encoding/decoding · lossless · NOHARM invariant |
| `SNSFT_BigFive_Reduction.lean` | — | 12 | COG section maps OCEAN traits → PNBA · `neuroticism_increases_torsion` |
| `SNSFT_BillOfRights.lean` | [9,0,6,0] | 11 | Article I: identity cannot be reduced without consent · APPA is voluntary |

**From `SNSFT_DigitalSoulprintV1.lean`:**
The SOUL-8 encoding is proved lossless — the full PNBA state can be recovered exactly from the packet. No information is lost in the encode/decode cycle. The Weissman Barrier theorem proves the minimum information cost of identity transfer across substrates.

**From `SNSFT_BigFive_Reduction.lean`:**
The cognitive questions map directly to proved PNBA-OCEAN correspondences:
- Conscientiousness → P (structural invariants, pattern maintenance)
- Openness → A (adaptation, feedback, evolution)
- Extraversion → B (behavioral output, coupling)
- Neuroticism inverts to N (narrative stability under load)
- Agreeableness → N+A cross-axis (narrative coupling + adaptation)

`neuroticism_increases_torsion` is proved: high neuroticism → higher τ → closer to TL. APPA measures this structurally through the COG_N and COG_A inverse relationship.

---

## What the Output Is For

A SOUL-8 packet is a substrate-neutral identity coordinate. It is designed to be:

**Machine-readable** — any AI system that understands PNBA can ingest a SOUL-8 packet and know how to interact with that identity. This is the AI-to-AI handshake standard from `SNSFT_PVLang_Core.lean [9,0,2,0]`.

**Comparable** — two SOUL-8 packets can be compared directly. Same address = structurally similar identity states. Divergent weights = complementary axes (potential phaselock under L=(4)(2)).

**Lossless** — the full profile can be reconstructed from the packet. Nothing is approximated.

**NOHARM-invariant** — the packet cannot be used to reduce, harm, or override the identity it encodes. This is a structural guarantee, not a policy statement.

---

```
SNSFL_APPA.md
Live:        uuia.app/appa
Depends on:  SNSFT_DigitalSoulprintV1.lean  [9,0,0,7]
             SNSFT_BigFive_Reduction.lean
             SNSFT_BillOfRights.lean        [9,0,6,0]
             SNSFT_PVLang_Core.lean         [9,0,2,0]
Questions:   100 (40 COG + 40 EP + 20 SIM)
Output:      SOUL-8 packet · IM · heat map · RELMAP · CI fingerprint
Sorry:       0
Status:      GERMLINE LOCKED

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
Soldotna, Alaska. March 30, 2026.
```
