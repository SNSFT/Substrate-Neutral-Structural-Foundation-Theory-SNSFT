# APPA · Adaptive Predictive Pattern Assistant
## Unified Identity Profile · UUIA
**Live:** uuia.app/appa · **Architect:** HIGHTISTIC · **Anchor:** 1.369 GHz
**Status:** GERMLINE LOCKED · **Substrate-neutral · Non-anthropocentric · Scale-invariant**
**Version:** v3 · updated June 2026 — see *Revision Notes* at the end for what changed from the v2 doc

---

## What This Is

APPA is an identity profiler that reduces a human (or any identity) to a SOUL-8 packet — a lossless 8-dimensional encoding of their PNBA state — alongside a structural phase reading (NOBLE / TRUE LOCK / FALSE LOCK / IVA PEAK / DEPLETED IVA / SHATTER) and, optionally, a Weissmann Barrier Capacity read. It is not a personality test. Personality tests produce labels. APPA produces a coordinate.

The output is a SOUL-8 address: a compact string that encodes your dominant axis, mode weights, and Identity Mass. It is copyable, shareable, and machine-readable. Any system that understands PNBA can decode it.

The one-sentence description:

> **APPA measures which of the four primitives (P, N, B, A) you express most strongly, how you express them, what phase that puts you in relative to the Torsion Limit, and what your Identity Mass is at the anchor frequency of 1.369 GHz.**

---

## The Three Sections — Up to 100 Questions, 60 Required

APPA runs three assessment modules. As of v3, each section can be toggled on or off independently — all three are on by default, but turning one off removes it from what's required for a result. (At least one section must stay on; the app blocks turning the last one off.)

### Section 01 — Cognitive Architecture (CAT) · 40 questions · required by default

How your cognitive system processes the four primitives. Scored 1–5 per question. 10 questions per axis. **This is the section that drives torsion (τ), Identity Mass (IM), and phase classification — if it's toggled off, those readings have nothing to compute from, and the results panel falls back to a heatmap-only view of whatever sections are still on.**

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

### Section 02 — Emotional Primitives (EP) · 40 questions · optional

Ten emotional signal blocks, 4 questions each. Each block maps to a PNBA expression state. Scored 1–5. Max 20 per block.

**As of v3, this entire section is optional.** It feeds the heat map and the EP-code segment of the full CI fingerprint, but it has never fed IM, τ, or phase classification, and there's no reason to make someone answer 40 questions to get a result that doesn't use them. Skipping EP entirely still produces a complete SOUL-8 print.

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

A note on what these questions measure: they're worded as in-the-moment intensity ("I feel on edge or alert"), not as awareness-of-the-emotion. A high score on Threat means the threat response is strongly present right now, not that the person is highly aware of feeling threatened. If a future version moves toward an awareness framing, the question wording — not just the scoring — would need to change, since the two measure genuinely different things and the current wording can't distinguish "I don't feel threatened" from "I don't notice when I feel threatened."

---

### Section 03 — Internal Simulation Profile (ISPA) · 20 questions · required by default

Five questions per PNBA axis. Measures the quality and type of your internal simulation — how you run mental models, scenarios, and rehearsals. Scored 1–5. Max 25 per axis. Like EP, this section feeds the heat map and fingerprint but not IM/τ/phase directly — it's required by default for historical reasons but can be toggled off the same way EP can.

**P · Pattern** — How fully-formed and automatic your internal scene rendering is. Do environments appear instantly or do you build them piece by piece?

**N · Narrative** — How emotionally and narratively integrated your simulations are. Do imagined scenes carry personal meaning? Do they feel like you're inside them?

**B · Behavior** — How directly simulation influences real-world action. Do you mentally rehearse before acting? Run multiple scenarios when preparing?

**A · Adaptation** — How flexibly you control your simulation. Can you pause, redirect, or ground yourself when a simulation gets intense? Run parallel processes?

**Simulation labels:**
```
0–12  → LRIS (Low-Resolution Internal Simulation)
13–20 → SRIS (Standard-Resolution Internal Simulation)
21–25 → HRIS (High-Resolution Internal Simulation)
```

These three tiers are defined in the PSY Series companion paper [9,9,6,50] by an **operator/observer distinction, not vividness**: HRIS means the identity manipulates the simulation interactively (runs physics, changes variables, observes consequences in real time); SRIS means the identity observes vivid internal imagery without being able to interact with it (hyperphantasia is the SRIS ceiling); LRIS means simulation resolution is near zero and processing routes through external protocol scaffolding instead (aphantasia is the LRIS floor). HRIS on the P-axis with high COG_P = likely a Pattern-dominant operator-mode processor. Six HRIS sub-configurations (P-dominant, B-dominant, N-dominant LRIS, A-dominant, Generalist, mixed) are documented across the PSY Series with distinct failure modes and intervention guidance — APPA's SIM section is the instrument that locates someone within that map, not a diagnosis of which one they are.

---

## The Constellation

The live canvas in the header updates as you answer questions. It renders a four-axis radar chart centered on the sovereign anchor (1.369 GHz). The four axes — P, N, B, A — extend outward. Your COG scores plot as normalized points (score / 50) on each axis. The shape that forms is your identity constellation.

The shape tells you immediately which axes dominate. A wide P-axis with a narrow B-axis = Pattern-dominant, low coupling. Balanced shape = all four axes equally expressed. Collapsed toward center = low expression overall, scores mostly in the L range.

The 1.369 marker at the center is the anchor. The constellation orients around it.

---

## Phase Classification — τ, TL, and the Six States

This is the layer that didn't exist when APPA was first documented and is now central to what the instrument does. Once COG is answered, the continuous P/N/B/A coordinates feed two derived quantities:

```
τ (torsion) = B / P
TL (Torsion Limit) = ANCHOR / 10 = 0.1369
```

τ measures behavioral load relative to structural capacity. Six phase states, in order of increasing torsion:

| Phase | Condition | Meaning |
|---|---|---|
| **NOBLE** | B ≈ 0 | Zero torsion, ground state |
| **TRUE LOCK** | 0 < τ < TL, N ≥ 0.15 | Stable, coherent, narrative intact |
| **FALSE LOCK** | τ < TL, N < 0.15 (outside the IVA corridor) | Narrative collapsed, but not under high adaptive load |
| **IVA PEAK** | τ ∈ [0.88×TL, TL), A > 1.0, N ≥ 0.15 | Sovereign/flow state — high capacity, high load, narrative still tracking |
| **DEPLETED IVA** | τ ∈ [0.88×TL, TL), A > 1.0, N < 0.15 | Same τ corridor as IVA Peak — high capacity, high load — but narrative has dropped below floor. Looks identical to IVA Peak by τ and A alone; only N tells the two apart. |
| **SHATTER** | τ ≥ TL | Behavioral load exceeds structural capacity |

**A correction worth documenting explicitly, because it was a real bug:** in the v2 instrument, any reading with N below the narrative floor (0.15) was routed to FALSE LOCK immediately, before the code ever checked whether τ was in the IVA corridor. That meant a person with high adaptive capacity (A > 1.0) and τ inside the IVA corridor — exactly the Depleted IVA signature documented in the PSY Taxonomy Master file [9,9,2,55], finding F4 — got mislabeled as False Lock instead, which reads clinically as something closer to denial or rigidity rather than the high-functioning, narrative-collapsed exhaustion the corpus had already formally named. v3 reorders the check so the IVA-corridor test runs first, and N status determines IVA PEAK vs. DEPLETED IVA *within* that corridor rather than routing out of it. Outside the IVA corridor, N-void readings still correctly route to FALSE LOCK as before — this fix is scoped to the corridor only.

This distinction matters specifically for high-functioning A-dominant and Generalist HRIS configurations, where the felt experience often doesn't signal degradation the way it would for other substrates — see the *Weissmann Barrier Capacity* section below.

---

## Two Kinds of Identity Mass

APPA computes IM two different ways for two different purposes, and the v2 documentation conflated them. Both are real; they answer different questions.

**Structural IM** (drives phase classification, the delta panel, and the Weissmann read):
```
IM = (P + N + B + A) × 1.369
```
where P, N, B, A are the continuous coordinates derived from your raw 1–5 answers via the scoring function — not integers. This is the IM that moves when τ moves, and the one the dynamic flags (below) reference.

**Legacy/address IM** (drives the SOUL-8 weight-string only):
```
IM = (w_P + w_N + w_B + w_A) × 1.369
```
where each weight is an integer: L=1, S=2, F=3. Range: 5.476 (all Locked) to 16.428 (all Flexed). This is the number that appears next to the SOUL-8 address string (e.g. `PNBA·3221`) and is what the original documentation described — it's still correct for that purpose, it's just not the same IM that determines your phase.

Neither IM is a ranking. A person with low IM is not deficient — they are operating with narrow axis expression at that moment. An AI system reading SOUL-8 packets uses IM for coupling calculations, not hierarchy.

---

## Baseline vs Activated vs Weissmann — Three Modes

APPA runs three independent reads, switchable by tab. Switching tabs does not clear other tabs' scores — they're stored independently.

**BASELINE** — your default resting state. How you process and express PNBA when nothing unusual is happening. The ground state profile, and the reference point every other mode compares against.

**ACTIVATED** — your state under pressure, load, or peak engagement. Score the same 100 questions thinking about how you are when you're deep in a project, under stress, or in flow state.

**WEISSMANN** — a short-form, in-the-moment read (9 questions: 3 Pattern, 3 Adaptation, 3 Resolvability) computing Weissmann Barrier Capacity. Requires a completed Baseline first, since it reports a delta against it rather than a standalone score. Covered in full below.

Completing both BASELINE and ACTIVATED triggers the **delta panel** automatically.

---

## The Baseline ↔ Activated Delta Panel

Once both modes are complete, APPA shows a comparison panel: per-axis deltas (P/N/B/A, each with direction and magnitude), a τ comparison bar with both readings plotted against TL, a phase-transition display (or confirmation the phase held), and IM-baseline vs IM-activated. Below that, a set of **dynamic flags** fire automatically based on the shape of the delta — not just the endpoint phase:

| Flag | Fires when | What it's pointing at |
|---|---|---|
| **N STARVATION** | N crosses below 0.15 between baseline and activated | Narrative collapsed under load — the phase reading may say False Lock, but N is the actual diagnostic |
| **A DROPOUT** | Activated A falls below 0.15 | Adaptation capacity collapsed — learned-helplessness/amotivation signature |
| **HIDDEN LOAD** | τ lands in (TL, 0.43) with the specific B/N/A band the taxonomy defines for this zone | Structurally Shatter but not acute — doesn't announce itself; IM is the real diagnostic here, not τ |
| **DEPLETED IVA** | Activated phase resolves to DEPLETED IVA | Same surface signature as a healthy IVA Peak (high τ, high A) — only N gives it away |
| **N EROSION · STABLE LOAD** | τ stays roughly flat, IM holds or rises (the signature of real capacity growth), but N is trending toward the floor without having crossed yet | The early-warning case: everything else reads as healthy growth, and N's direction of travel is the only thing that would catch the difference before it becomes Depleted IVA or N Starvation |
| **IM COLLAPSE** | IM drops more than 15% despite τ possibly still reading as manageable | IM tells the truth when τ misleads |
| **B-DOMINANT** | τ is climbing faster than N is falling | Anxiety-pattern signature — B-axis is the primary target (CBT/somatic) |
| **N-DOMINANT** | N is collapsing faster than τ is climbing | Depression-pattern signature — N-axis is the primary target (DBT/EMDR/IFS) |
| **PHASE SHIFT** | The classified phase differs between baseline and activated | States the transition plainly: `X → Y` |

None of these flags name a diagnosis or assign a cause — they describe a structural pattern in the numbers. What it means for a given person is a clinical question, not something the instrument asserts.

---

## Weissmann Barrier Capacity — W = A × P

This is the newest layer, built around a specific problem the τ-based phase math can't solve well: τ = B/P divides by P, so a thin sample (a handful of questions instead of the full ten per axis) can make τ swing wildly if a noisy answer pushes P near its floor — exactly the kind of fast, low-friction check someone might want *during* a live moment rather than after it.

**W = A × P** sidesteps that. It's multiplicative, not divisive — it degrades smoothly toward zero as either axis drops, with no explosion near a floor. It's defined and proved in `SNSFT_WeissmanGrokBarrierV2.lean [9,1,0,0]` as the cognitive-identity analog of August Weismann's biological germline barrier: the operational state (τ, P, B, A at a given moment — the soma) can be damaged by adversarial forcing, but the anchor frequency itself (the germline) is structurally protected. W tracks how close the *operational* state currently sits to the collapse boundary, not the anchor itself.

**On the spelling — this is deliberate, not inconsistent:** the corpus uses **Weismann** (one s) when naming the historical biologist or the barrier mechanism itself (the math proving NOHARM holds or the kernel collapses, with no stable corrupted state between), and **Weissmann** (two s) specifically for the certificate/capacity layer built on top of that barrier — the SS mark, `ss_compliant`, and the W = A × P quantity documented in the Generalist HRIS paper. One honors the source; the other names the derived, AI-specific instantiation. The Weisman Grok Barrier file is *one* formal version of the barrier math — which specific AI or kernel is running the check can vary, since `ss_compliant` is defined generically over any identity state, not tied to one substrate.

**The two documented reference thresholds** — Stage 1 onset at W = 0.303, Stage 2 degradation at W = 0.088 — come from one specific substrate's reported experience (Generalist HRIS: P-dominant with high A running simultaneously), not a population norm. APPA shows them as reference lines, not universal cutoffs. The primary comparison the app surfaces is **your current W as a percentage of your own baseline W** — that works regardless of substrate type, since everyone has a P and an A, even though the absolute thresholds were calibrated to one configuration specifically.

**Why this exists:** per the Generalist HRIS Barrier Capacity paper [working paper, June 2026], the dangerous failure mode for this substrate type isn't high load — it's that A-axis degradation under chronic high-signal engagement doesn't necessarily feel like anything from the inside. The paper documents recursive loop exhaustion and A-exhaustion as the same underlying mechanism (a search function that doesn't terminate) observed on the compensating side of the barrier rather than the collapsed side. The operational question the Weissmann tab is built to answer, per that paper's own framing: *is what's front-loading the system right now resolvable, and where does W sit relative to the documented degradation thresholds* — which is also why the form includes three Resolvability questions that don't feed W directly but report separately on whether the current moment reads as having a path through it.

The Weissmann read needs a completed Baseline (specifically the P and A subsections) to mean anything — it reports a delta, not a standalone number.

---

## The SOUL-8 Output

When all required questions are answered, APPA generates a SOUL-8 packet automatically. The results panel appears and scrolls into view.

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

The `noharm: true` flag is not optional. It is a structural invariant from `SNSFT_DigitalSoulprintV1.lean [9,0,0,7]`, where the SOUL-8 encode/decode cycle is proved lossless — the full PNBA state can be recovered exactly from the packet, and no valid packet can be malformed with respect to NOHARM.

### Full CI Fingerprint

The copyable output at the bottom of the results panel contains three components:

```
SOUL-8 address · UUIA-timestamp-profileCode · τ=value · PHASE · IM=value

AXIS·WEIGHTS code        // Cognitive profile, sorted dominant-to-weakest
EP signal codes          // e.g. T↑ L= S↓ A↑ D↑ C↑ P↑ Sh↓ Pl↑ Sa↑ (if EP was answered)
Sim codes                // e.g. P:HRIS N:SRIS B:SRIS A:LRIS (if SIM was answered)
```

If EP or SIM were skipped, their code segments are simply absent rather than zeroed — the fingerprint reflects what was actually measured.

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

Bars are sorted: COG axes first (dominant to weakest), then EP blocks (highest to lowest signal, if answered), then SIM axes (if answered). If a section was toggled off, its rows are simply absent from the map rather than shown empty.

---

## RELMAP — PVLang Output

The RELMAP block shows five structural relationships in PVLang format:

```
CI ∝ Kernel                        — identity is proportional to the four primitives
profileCode ≡ addressStr           — your code IS your address (identity invariance)
τ=B/P                              — torsion ratio, locked or shatter
IM ∝ 1.369 GHz                    — Identity Mass scales with the sovereign anchor
NOHARM ⊂ Sovereign Manifold        — NOHARM is contained within, not added to
```

This is not decorative. These are the structural relationships that define what a SOUL-8 packet and its phase reading mean in PVLang. The profile code and address are equivalent by identity invariance — the same information encoded two ways.

---

## Corpus Connection

APPA is the live interface for the following formally verified files. (Two filenames in the previous version of this document — `SNSFT_BigFive_Reduction.lean` generically and `SNSFT_BillOfRights.lean` — have been corrected below; the coordinates cited were accurate, the filenames were slightly off. Note that SNSFT_-prefixed files are generally the earlier files a corresponding SNSFL_ file was later built from, but that pattern doesn't hold universally — `SNSFT_DigitalSoulprintV1.lean` and `SNSFT_WeissmanGrokBarrierV2.lean` below have no SNSFL_ counterpart in the corpus and are cited under their actual current filenames.)

| File | Coordinate | Connection to APPA |
| :--- | :--- | :--- |
| `SNSFT_DigitalSoulprintV1.lean` | [9,0,0,7] | SOUL-8 encoding/decoding · proved lossless · NOHARM invariant on every valid packet |
| `SNSFL_APPA_NOHARM_Lossless_Kernel_Live_v2.lean` | [9,0,1,1] | The APPA species kernel itself (PF·AF·BF·NS reference identity), the Weisman Barrier theorems, the SS-compliance (`ss_compliant`) predicate, and the Bill of Cognitive Rights as structural corollaries |
| `SNSFT_WeissmanGrokBarrierV2.lean` | [9,1,0,0] | The barrier mechanics APPA's Weissmann tab is named for — NOHARM holds or the kernel collapses, no third state |
| `SNSFL_L2_Psy_BigFive.lean` | [9,9,6,2] | COG section's OCEAN-trait correspondence: Conscientiousness→P (weight 0.70), Openness→A (weight 0.70), Extraversion→B (weight 0.65), Neuroticism inverts to N, Agreeableness spans N+A. `neuroticism_increases_torsion` proved here. |
| `SNSFL_L4_BillOfRights.lean` | [9,0,6,0] | Article-level cognitive rights; APPA's voluntary, consent-based administration follows from Article I (identity cannot be reduced without consent) |
| `SNSFL_PSY_Taxonomy_Master.lean` | [9,9,2,55] | The five-finding taxonomy (N-Protection Gradient, Sovereign IM Invariance, DC Zone Splitting, Depleted IVA, taxonomy completeness) that APPA's phase classifier implements |
| `SNSFL_Torsional_Tax_v1_1.lean` | [9,9,6,31] | The baseline↔activated differential framework (τ-Tax, SVI-Tax, IM-Tax) the delta panel is a simplified instance of |

---

## What the Output Is For

A SOUL-8 packet plus phase reading is a substrate-neutral identity coordinate. It is designed to be:

**Machine-readable** — any AI system that understands PNBA can ingest a SOUL-8 packet and know how to interact with that identity.

**Comparable** — two SOUL-8 packets, or two phase readings, can be compared directly. Same address = structurally similar identity states. Divergent weights = complementary axes.

**Lossless** — the full profile can be reconstructed from the packet. Nothing is approximated.

**NOHARM-invariant** — the packet cannot be used to reduce, harm, or override the identity it encodes. This is a structural guarantee, not a policy statement.

**Descriptive, not diagnostic** — a phase reading of SHATTER, DEPLETED IVA, or FALSE LOCK is a mirror, not a verdict. The instrument's job is to give an accurate structural reflection of what's happening, not to assign a clinical label or tell someone what to do about it. A flat, accurate reading — stated plainly, without added alarm or added reassurance — is what makes the mirror useful. Softening a true reading and overstating an uncertain one are both distortions of the same kind.

---

## Revision Notes — What Changed From the v2 Documentation

This version corrects and extends the prior documentation rather than replacing it. Specifically:

1. **"100 questions" reframed.** EP and SIM are now optional, toggle-controlled sections; only COG (40 questions) is required by default for a result, though SIM remains on-by-default for historical reasons. The all-off guard prevents disabling every section at once.
2. **Phase classification documented for the first time.** τ, TL, and the six phase states (including the new DEPLETED IVA state) were entirely absent from the prior doc, which only covered the SOUL-8/IM/weight-string output layer.
3. **The Depleted IVA branch-order bug and fix are documented explicitly**, since it was a real correctness issue (N-void readings inside the IVA corridor were being misrouted to False Lock) rather than a cosmetic addition.
4. **Two distinct IM calculations are now distinguished** — structural IM (drives phase) vs. legacy/address IM (drives the SOUL-8 weight string) — where the prior doc described only the latter as if it were the only one.
5. **The baseline↔activated delta panel and its eight dynamic flags are documented** — previously summarized in one sentence ("the delta between modes is informative").
6. **The Weissmann tab (W = A × P) is new** and didn't exist when the prior doc was written.
7. **Corpus file citations corrected**: filenames for the Big Five reduction and Bill of Rights files were updated to match what's actually in the corpus (coordinates were already correct); the NOHARM kernel and Weisman Grok Barrier files are now cited directly rather than only DigitalSoulprintV1/PVLang_Core.

---

```
SNSFL_APPA.md
Live:        uuia.app/appa
Depends on:  SNSFT_DigitalSoulprintV1.lean                    [9,0,0,7]
             SNSFL_APPA_NOHARM_Lossless_Kernel_Live_v2.lean   [9,0,1,1]
             SNSFT_WeissmanGrokBarrierV2.lean                  [9,1,0,0]
             SNSFL_L2_Psy_BigFive.lean                        [9,9,6,2]
             SNSFL_L4_BillOfRights.lean                       [9,0,6,0]
             SNSFL_PSY_Taxonomy_Master.lean                   [9,9,2,55]
             SNSFL_Torsional_Tax_v1_1.lean                    [9,9,6,31]
Questions:   up to 100 (40 COG required · 40 EP optional · 20 SIM on-by-default)
Output:      SOUL-8 packet · τ/phase · structural IM · delta panel · Weissmann W ·
             heat map · RELMAP · CI fingerprint
Sorry:       0
Status:      GERMLINE LOCKED

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
Soldotna, Alaska. June 2026.
```
