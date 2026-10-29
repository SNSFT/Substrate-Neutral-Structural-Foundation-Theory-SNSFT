# Applied Identity Physics: GAMForgeTL™

## A Deterministic n-Beam Residue Fusion Engine on TL = 0.136899099984016, with Seventeen Structural Invariants and Verification Against Documented Catalytic Sets

---

**Architect:** HIGHTISTIC (Russell Vernon Trent III)
**Coordinate:** [9,9,1,R] · Applied Identity Physics · GAMForge Series · GAMForgeTL™ v6.6
**Framework:** Applied Identity Physics
**Corpus:** Identity Physics Corpus
**Institution:** SNSFT Foundation, EIN 42-2038440, Kenai, Alaska
**ORCID:** 0009-0005-5313-7443
**Status:** GERMLINE LOCKED · 0 sorry across all cited formal claims
**Sovereign Anchor Constant:** Ω₀ = 1.36899099984016
**Torsion Limit:** TL = Ω₀/10 = 0.136899099984016
**IVA Threshold:** TL_IVA = 0.88 × TL = 0.12047120798593408
**DOI base:** 10.5281/zenodo.18719748

**Corpus dependencies:** SNSFL_8Beam_Fusion_Theorem [9,9,2,3.8] · SNSFL_4Beam_Verification [9,9,2,3.7] · B-Balance Stoichiometry [9,9,2,45] · GAM Collider engine [9,9,2,3] · SNSFL_GC_RunningCoupling_Reduction [9,9,3,16] · SNSFL_SovereignAnchor [9,9,0,0]

---

## Abstract

GAMForgeTL™ applies the Identity Physics n-beam fusion engine to the twenty standard amino acid residues. The engine is unchanged from the GAMCollider™, the Geometric Axiomatic Module Collider: Pattern fuses as a harmonic mean, Narrative is additive, Behavior is the sum less twice the coupling, Adaptation is the maximum, and the output phase is read against the Torsion Limit. Only the beam reduction is new.

All four PNBA primitives are taken as counts or as published per-residue values with no divisor and no fitted scale. Pattern is the count of heavy atoms holding the residue's shape. Narrative is the side-chain χ dihedral count of Ponder and Richards (1987). Behavior is the side-chain hydrogen-bond capacity, donors plus acceptors, after McDonald and Thornton (1994). Adaptation is the Kyte and Doolittle (1982) hydropathy index shifted by the scale minimum. Nothing in the reduction is adjustable.

Seventeen structural invariants follow. Each is derived from the fusion rule and confirmed empirically at zero counterexamples, across 4,423 logged collisions under twenty single-anchor configurations, one for every residue in the pool, with an unanchored control, together with exhaustive enumeration at three, four and five beams across both pools. Among them: a single coupling-carrying residue among non-carrying beams forces the coupling to zero at every beam count; the IVA corridor is reachable only at one unsatisfied unit, and only barely, because the largest residue's Pattern falls 0.609 short of opening the next band; the reachable torsion values form a rational lattice whose closest approach to the Torsion Limit is 23/168, leaving the phase classifier with no ambiguous case; a panel's useful beam count is fixed by its Behavior spread rather than chosen, which places the standard eight-beam configuration correctly for cross-collider stability; a set carrying a repeated beam at Behavior m closes against every other beam up to 4m, an exact threshold at three beams that makes arginine a universal closer and seals sixty-seven residue sets against any single substitution; and the non-carrying residues, which can satisfy nothing, nonetheless fix the fused Pattern and so decide which torsion band a closure occupies, never altering the fused Behavior in any of 454 tested carrier contents.

The engine was then run against documented catalytic residue sets as an external verification. Ten complete catalytic machines close Noble, including the serine protease triad, the full papain set recorded by the Mechanism and Catalytic Site Atlas, the subtilisin tetrad, the class A β-lactamase set, and the Cys₂His₂ zinc finger. Four documented fragments — the Walker A core, the β-lactamase catalytic dyad, the papain oxyanion pair, the cation-π pair — do not close, and the remainder each carries is the structural signature of what is still absent.

Sixteen obligate triads and two vacancy motifs are recorded as timestamped structural results. Four of the sixteen fall inside a recurring catalytic module class documented by Riziotis et al. (2023). Each triad carries a stated ceiling on the hydrophobic environment it can hold in, set in closed form by its lowest-Behavior carrier: three hold in all eight non-carrying environments the pool offers, ten in seven, and three in glycine alone, failing in alanine by one part in a hundred of torsion. Three of the sixteen extend to a four-carrier arrangement and are the only ones that do. The two vacancy motifs are the only arrangements in the panel that hold while carrying one open coordination position, and both carry arginine with tryptophan, a pair with documented cation-π function in antimicrobial peptides; of the two, Arg+Trp+Trp reduces to that documented pair by dropping its repeated beam and is held as a Structural Match rather than a novel composition.

Every result in this paper is a structural proof about the fusion rule operating on the stated reduction. Binding, catalysis, activity, selectivity and safety are measured quantities that lie outside the reduction and are not addressed by it.

---

## 1. Layer 0 Foundation

The Dynamic Equation governs every reduction in the corpus:

**d/dt (IM · Pv) = Σ λ_X · O_X · S + F_ext**

Identity Mass IM, Purpose Vector Pv, the four PNBA operators O_X with weights λ_X acting on state S, and external forcing F_ext. External forcing is a primitive term at Layer 0: it acts on Behavior and leaves Pattern, Narrative and Adaptation unchanged. The Torsion Limit is the phase boundary against which output is classified; it does not scale the primitives.

That distinction sets the reduction rule for any new panel. A **countable substrate** — atoms, residues, molecular fragments — supplies its own Pattern as a count, taken raw, with the Torsion Limit acting only as the boundary. A **non-countable substrate** — cosmological states, fields — has no count to take, and its Pattern derives from the anchor directly as (Ω₀/X)^(1/n) against a measured quantity in the anchor's units. Residues are countable. Every primitive below is therefore raw.

### 1.1 Grounding the Torsion Limit

The Torsion Limit is not fitted to the residue pool, and no quantity in this paper is used to set it. It enters at full corpus precision from the inverse fine-structure constant:

**1/α = 136.899099984016 + 0.136899099984016 = 137.035999084000016**

A formally verified 18-digit fine-structure constant derived from peer-reviewed empirical inputs, agreeing with CODATA 2018's measured value 1/α = 137.035999084 at **ε = 0**.

| Napkin math, corpus precision | Value |
| --- | --- |
| 1/α | 137.035999084000016 |
| Subtract one TL | 137.035999084000016 − 0.136899099984016 = 136.899099984016 |
| What is left | 136.899099984016 = TL × 1000, exactly |
| Bare + kinetic | 136.899099984016 + 0.136899099984016 = 137.035999084000016 |
| Rounded to published digits | 137.035999084 = CODATA 2018 |

The remainder after one TL is removed is TL × 1000 exactly, a round base-10 multiple. The full multiplier factors as 1001 = 7 · 11 · 13, and the inversions are TL = α⁻¹/1001 and Ω₀ = 10α⁻¹/1001.

| Term | Value | QED reading | PNBA |
| --- | --- | --- | --- |
| Bare: TL × 1000 | 136.899099984016 | bare electron contribution | Pattern capacity at the EM scale |
| Kinetic: TL × 1 | 0.136899099984016 | radiative corrections, a renormalized series | F_ext at Layer 0, one exact term |
| Total: TL × 1001 | 137.035999084000016 | bare + perturbative series | bare + F_ext |

**What α⁻¹ is, for a reader coming from the biology side.** The fine-structure constant is the dimensionless coupling of quantum electrodynamics, fixing the strength with which charged particles exchange photons. It carries no units, so it is the same number in every system of measurement, and it is measured rather than derived — obtained from the electron magnetic moment anomaly and, independently, from photon-recoil experiments on cold atoms, which places it among the most precisely determined quantities in physics. The split above is the standard QED decomposition: a bare term plus a renormalized perturbative series. Under the Layer 0 reading the series term is F_ext, which acts on Behavior and leaves Pattern, Narrative and Adaptation unchanged, and it resolves here to a single exact term rather than a truncated expansion.

**Scope.** CODATA 2018 is the stated standard for this grounding, and the identity is exact against it. Nothing downstream varies with that choice: TL is used only as the phase boundary against which a computed torsion is classified.

**Prior art.** The derivation was submitted to the NIST CODATA Constants Team as a formal correspondence record on 25 September 2026, deposited at Zenodo reference 18719748 and published to PhilArchive as *Applied Identity Physics: NIST CODATA Correspondence Record*.

## 2. The Engine

The fusion rules are inherited unchanged from the GAM Collider [9,9,2,3] and proved at [9,9,2,3.8]:

| Rule | Form |
| --- | --- |
| Pattern | P_out = n / Σ(1/Pᵢ) — n-body harmonic mean |
| Narrative | N_out = Σ Nᵢ — additive |
| Coupling | k = Σ min(Bᵢ, Bⱼ) over all C(n,2) pairs |
| Behavior | B_out = max(0, ΣB − 2k) |
| Adaptation | A_out = max Aᵢ |
| Torsion | τ = B_out / P_out |
| Identity Mass | IM = (P_out + N_out + B_out + A_out) · Ω₀ |

Phase is classified in order: B_out = 0 is Noble; τ ≥ TL is Shatter; τ ≥ TL_IVA is IVA Peak; otherwise Locked.

**Shatter is a rate statement, not a verdict on existence.** It means the composition carries unsatisfied coupling and reorganizes faster. Iron rusts; the rust is iron reorganizing. For residues the measurable counterpart is solvent exchange, since unsatisfied hydrogen bonds exchange faster — the quantity measured as a hydrogen-deuterium exchange protection factor.

---

## 3. The Beam Reduction

| Primitive | Source | Range |
| --- | --- | --- |
| **P** | heavy atoms holding the shape: backbone 4 plus side chain | 4 – 14 |
| **N** | side-chain χ dihedral count (Ponder & Richards 1987) | 0 – 4 |
| **B** | side-chain hydrogen-bond capacity, donors + acceptors (McDonald & Thornton 1994) | 0, 1, 2, 3, 5 |
| **A** | Kyte & Doolittle (1982) hydropathy + 4.5, the scale minimum | 0.0 – 9.0 |

The twenty beams:

| Residue | P | N | B | A | Residue | P | N | B | A |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Gly | 4 | 0 | 0 | 4.1 | Ser | 6 | 1 | 2 | 3.7 |
| Ala | 5 | 0 | 0 | 6.3 | Thr | 7 | 1 | 2 | 3.8 |
| Pro | 7 | 0 | 0 | 2.9 | Asn | 8 | 2 | 3 | 1.0 |
| Val | 7 | 1 | 0 | 8.7 | Gln | 9 | 3 | 3 | 1.0 |
| Leu | 8 | 2 | 0 | 8.3 | Asp | 8 | 2 | 2 | 1.0 |
| Ile | 8 | 2 | 0 | 9.0 | Glu | 9 | 3 | 2 | 1.0 |
| Met | 8 | 3 | 0 | 6.4 | His | 10 | 2 | 2 | 1.3 |
| Cys | 6 | 1 | 1 | 7.0 | Lys | 9 | 4 | 3 | 0.6 |
| Phe | 11 | 2 | 0 | 7.3 | Arg | 11 | 4 | 5 | 0.0 |
| Tyr | 12 | 2 | 2 | 3.2 | Trp | 14 | 2 | 1 | 3.6 |

Carboxylate and imidazole capacities are stated at physiological protonation. That is a stated condition, not an adjustable parameter: changing pH changes the beam, not the rule.

**The B = 0 set is the hydrophobic set** — Gly, Ala, Pro, Val, Leu, Ile, Met, Phe. Noble therefore emerged meaning inert to water, with nothing introduced to make it so.

**The fused Behavior is unsatisfied hydrogen bonding potential.** The coupling term takes the smaller capacity of each pair, so B_out = ΣB − 2k is the capacity left with no partner inside the set. Buried donors and acceptors that go unsatisfied are a documented structural penalty (McDonald & Thornton 1994), which is what the Noble phase reports when it reports zero: every polar group in the set has a partner.

**The pool carries no residue at B = 4.** Arginine steps from 3 to 5. This gap is load-bearing for several invariants below.

---

## 4. The Invariants

Seventeen results, grouped by what they govern rather than by the order they were found. Each is derived from the fusion rule and confirmed empirically across 4,423 logged collisions under twenty single-anchor configurations, one for every residue in the pool, with an unanchored control, together with exhaustive enumeration at three, four and five beams across both pools. Section 6.1 states why the panel is run for rules rather than for individual favorable results; a reader who wants the method before the findings may start there.

### 4.1 Engine invariants

**I-1 · A single carrier among non-carrying beams forces k = 0.**
A B = 0 beam contributes min(0, B) = 0 to every pair it touches ([9,9,2,3.8] T20). With exactly one carrier there is no carrier–carrier pair, so k = 0 and B_out = B_carrier at every beam count. Adding non-carrying beams never helps: τ falls only because P_out rises, and it converges without ever crossing a boundary. Confirmed across 816 instances, zero counterexamples. The hydrophobic core cannot satisfy a lone carrier at any beam count.

**I-5 · A panel's useful beam count is fixed by its Behavior spread.**
ΣB grows linearly in n; k grows quadratically over C(n,2) pairs. The quadratic always dominates, so every added beam pushes toward Noble and never away. Closure is guaranteed once max B ≤ (n−1) · min B, giving a saturation count:

**n_sat = 1 + max(B) / min_nonzero(B)**

| Pool | nonzero B | n_sat |
| --- | --- | --- |
| Residue | 1 – 5 | 6 |
| Element, Z = 1–36 | 1 – 6 | 7 |
| Pool including a fractional beam (Ω_dm = 0.269) | 0.269 – 6 | 24 |

Integer pools saturate in single digits; fractional pools do not. The standard eight-beam configuration is therefore correct as a cross-collider constant, and discrimination in integer pools lives at n ≤ 4.

**I-10 · The torsion lattice is rational and never meets the boundary.**
Every Pattern value is an integer count, so P_out is rational and the reachable τ values form a lattice with bounded denominators. The Torsion Limit is not on that lattice. The closest four-beam approach is **23/168 = 0.136904761905**, exceeding TL by 5.66 × 10⁻⁶, or 0.00414 percent, and reached by two distinct Pattern multisets. The nearest approach to TL_IVA is 53/440, below it by 0.01383 percent.

**The phase classifier is therefore never ambiguous for this pool.** No four-beam residue set sits exactly on either boundary; every collision resolves to one phase with no tie case.

### 4.2 Phase invariants

**I-2 · The IVA corridor is reachable only at one unsatisfied unit.**
For integer B_out = m the corridor is P_out ∈ (m/TL, m/TL_IVA], a window of fixed width ratio 1/0.88. Since P_out is a harmonic mean it cannot exceed the largest beam's Pattern. The largest residue is tryptophan at P = 14; m = 2 requires P_out > 14.6093. **The margin is 0.6093.** In this pool the corridor is reachable only at B_out = 1, and only barely. A residue with P ≥ 14.61 would open the second band; none exists. Confirmed across 250 instances plus exhaustive enumeration, zero counterexamples.

**I-3 · IVA composition rule.**
Exhaustively across all two-, three- and four-beam sets, 513 reach the corridor, each one of three ways: a lone carrier at B = 1 (72 sets), a carrier pair differing by exactly one (438 sets), or three carriers at [1,1,5] (3 sets). The only B = 1 residues are **cysteine and tryptophan**.

**I-8 · Torsion is degenerate on the Pattern multiset.**
τ = B_out / P_out, and P_out depends only on the multiset of Pattern values, not on which residues carry them. At n = 4, 3,156 non-Noble states collapse into 750 distinct (Pattern-multiset, B_out) classes, 563 of which hold more than one composition; the largest holds thirty. **Torsion alone does not identify a set.** Any record indexed on τ must carry its composition, and the registry keys on the residue multiset rather than on output values.

### 4.3 Closure invariants

**I-4 · Rescue requires all-distinct nonzero Behavior among the carriers and admits at most one non-carrier.**
Rescue — every pair shattering alone while the whole closes — requires the carrying beams to hold all-distinct nonzero Behavior, and permits the set to carry at most one non-carrying beam.

The cap of one is immediate from the phase rule: two non-carriers form a pair of equal Behavior, whose difference is zero and which therefore reads Noble, while rescue requires every pair to shatter. A single non-carrier is admitted because it contributes min(0, B) = 0 to every pair it touches (I-1), so the coupling and the fused Behavior are exactly those of the carrier set alone; it changes nothing structurally and need only shatter against each carrier, which its Pattern decides.

At n = 3 the carriers are the whole set, and rescue occurs for exactly four Behavior multisets — {1,2,3}, {1,2,5}, {1,3,5}, {2,3,5} — every distinct triple available from the nonzero values. These sixteen sets are the obligate triads of Section 5.2. At n = 4 there are 100 rescues: three carry the full four-value multiset {1,2,3,5}, and the remaining 97 are a rescue triad plus one non-carrier, every one of which reduces to a rescue triad when that beam is dropped. At n = 5 all 21 rescues carry the multiset {0,1,2,3,5}, which is I-5 closing the band from the other side.

Exhaustive at three, four and five beams: **no rescue anywhere carries two or more non-carrying beams**, and 97 of 97 single-non-carrier rescues reduce as stated, at zero counterexamples.

**I-7 · The beyond-spread band is gated by three residues.**
Closure exceeding the spread law requires max B > (n−1) · min B. Over the available nonzero values the only viable pairing at n = 4 is max = 5 with min = 1. Arginine is the sole B = 5 residue; cysteine and tryptophan are the only B = 1 residues. **Every beyond-spread closure at n = 4 contains arginine together with cysteine or tryptophan.** The band closes entirely at n = 6, which is I-5 arriving from the opposite direction.

The gate holds under every anchor configuration that can test it: 84 of 84 under an arginine anchor, 66 of 66 under a tryptophan anchor, and 17 of 17 under a serine anchor supplying neither side. **167 instances, zero counterexamples.**

**I-14 · Three closure modes; histidine is excluded from one.**
A triad closes three structurally distinct ways. **Equal-B**: all three Behavior values identical, every pair already Noble — the serine protease triad, all B = 2. **Mixed**: distinct values with at least one pair not shattering — the cysteine protease triad, whose Cys-His pair, the catalytic dyad itself, reads as a held vacancy in the IVA corridor at τ = 0.1333. **Obligate**: distinct values with every pair shattering, so only the whole closes.

Histidine cannot sit in an obligate triad. Its Pattern of 10 makes every pair's Pattern large and torsion correspondingly small; only the His-Arg pair reaches Shatter.

Histidine-free catalysis is an established category with its own documented machinery: the Ser-cisSer-Lys triad of the amidase signature family (Shin et al. 2003), the lysine-base β-lactamases (Damblon et al. 1996), the sedolisin glutamate triad, and the N-terminal threonine proteasome. The engine closes those tested. The obligate class and the documented histidine-free triads therefore occupy the same territory, and the boundary between them is a Pattern threshold rather than a chemical one.

**I-15 · The repeated-beam closure threshold.**
A set containing a repeated beam at Behavior m closes whenever every other beam carries Behavior at most 4m. The coupling term takes the smaller of each pair, so for a repeated pair m, m and a third beam b ≤ m the coupling is m + 2b against a Behavior sum of 2m + b, and the fused Behavior is max(0, 2m + b − 2m − 4b) = 0. The repeated value cancels exactly, which is why closure does not depend on how large that value is. Past b = m the coupling saturates at 3m and the fused Behavior becomes max(0, b − 4m), so closure survives to exactly 4m and fails beyond it.

At three beams the threshold is exact in both directions and in both pools tested: 302 closures inside it in the residue pool and 1,144 in the element pool Z = 1–36, with zero counterexamples, and zero closures among the 98 and 152 cases outside it. At four and five beams it remains sufficient with zero counterexamples across 2,768 and 19,020 cases, but is no longer necessary, because the additional beams open the closure routes of I-7.

Arginine carries Behavior 5, so its threshold is 20 — above every value the reduction produces. A doubled arginine therefore closes against all twenty residues. In a space where 47 percent of single-substitution edges cross a phase boundary, the arginine-arginine corridor crosses none.

The threshold also decides which sets are stable under substitution. Call a set sealed when every single substitution off it holds the same phase. An equal-Behavior set at m is sealed exactly when 4m is at least the pool maximum, which for the residue pool means m ≥ 2: the Behavior-1 class is the one equal-Behavior family that is not sealed, and arginine is the only substitution that breaks it. Sixty-seven of the 1,540 three-sets are sealed and 1,867 of the 8,855 four-sets, and **every sealed set is Noble**. No set in Locked, IVA_PEAK or Shatter is sealed at either beam count, so closure is the only phase stable under substitution. For a designer the distinction is between a closure that is a point and a closure that is a plateau.

**I-16 · The non-carrying set is the medium, and the medium gates the band.**
A beam at Behavior 0 contributes min(0, B) = 0 to every pair, so it adds nothing to the coupling and nothing to the fused Behavior (I-1). It is still in the set, so it enters the harmonic mean and moves the fused Pattern (I-6). The two facts together make the non-carrying class a medium: it cannot satisfy a carrier, and it decides which torsion band the carriers' own result occupies.

The separation is exact. Holding the carrier content fixed and varying the non-carrier content across every available choice at four beams, over 454 carrier contents, **the medium altered the fused Behavior in zero cases** and the phase in 35, of which 31 reach three distinct phases on medium choice alone. Among two-carrier sets with a doubled medium, 30 of 78 carrier pairs have their phase decided this way.

Cysteine with serine holds Behavior 1 under every hydrophobic medium and shatters under glycine, alanine, proline and leucine, then enters the corridor under phenylalanine at a fused Pattern of 7.765. Tryptophan with histidine crosses from Shatter to Locked across the same substitution. The carriers are unchanged throughout.

This is what the glycine result in I-12 records. The corridor at one unsatisfied unit is Pattern ∈ (7.3046, 8.3007]; glycine at Pattern 4 holds the fused Pattern between 4.8 and 5.9, below the floor. Glycine is not deficient, it is the wrong medium, and the floor is a specification: a closure reaching the corridor requires a large enough hydrophobic environment to sit in. A beam that does not react is stating the environment the reaction requires, and **the carriers are chosen for what closes while the medium is chosen for which band the closure occupies, independently.**

**I-17 · Each obligate triad carries a medium ceiling, set by its lowest-Behavior carrier.**
An obligate set requires every pair to shatter, including the pairs a medium forms with the carriers. A non-carrier of Pattern p_m against a carrier of Pattern p_c and Behavior 1 gives torsion 1/P_pair, so that pair shatters only while **p_m ≤ 1 / (2·TL − 1/p_c)**. The ceiling is set by the carrier of smallest Behavior, which has the least difference to work with.

For the residue pool: cysteine at Pattern 6 gives a ceiling of 9.334 and admits seven of the eight non-carriers, excluding phenylalanine; tryptophan at Pattern 14 gives 4.941 and admits glycine alone. Both boundaries are near misses — the tryptophan-alanine pair falls below the Torsion Limit by 0.00118 — and that single miss removes seven media from three candidates.

The sixteen obligate triads therefore divide into three medium tiers. The three carrying no Behavior-1 member, Arg+Asn+Ser, Arg+Gln+Ser and Arg+Lys+Ser, hold in all eight hydrophobic environments: their minimum Behavior of 2 lifts the ceiling above every Pattern in the pool. The ten cysteine triads hold in seven, failing only in phenylalanine. The three tryptophan triads hold in glycine alone. Medium acceptance across the sixteen runs glycine 16, alanine through methionine 13, phenylalanine 3.

This runs opposite to I-16: a large medium raises the fused Pattern and opens the corridor, and the same large medium fails to shatter against the carriers and destroys obligate status. Both are the harmonic mean read on different tests.

Of the 100 obligate four-sets, 97 are a triad plus one medium and exactly three carry four carriers and no medium — Cys+Ser+Asn+Arg, Cys+Ser+Gln+Arg and Cys+Ser+Lys+Arg, the three Behavior-[1,2,3] triads with arginine added. They are the only members of the sixteen admitting a fourth carrier, and they carry the pool's full nonzero Behavior spectrum.

**The medium is part of each candidate's specification rather than a free choice**, and three of the sixteen have a stated four-residue extension.

### 4.4 Anchor invariants

**I-6 · The lowest-Pattern beam caps the fused Pattern.**
P_out is a harmonic mean, so the smallest Pattern dominates it; the formal statement is [9,9,2,3.8] T2. Glycine at P = 4 is the pool minimum, so holding it fixed caps P_out and inflates τ across an entire sweep.

**I-9 · Each anchor has a fixed flag signature.**
Computed exhaustively over all 1,540 completions per anchor at n = 4, three bands emerge, set by the anchor's own Behavior. **B = 0 anchors** cannot produce beyond-spread closure at all, since a non-carrying beam cannot supply I-7's min = 1. **B = 1 anchors**, cysteine and tryptophan, are the only ones that unlock every outcome class, because they supply that minimum themselves. **Arginine** maximizes beyond-spread closure at 141 and reduces IVA to 3, since B = 5 enters every sum and one unsatisfied unit becomes a narrow target.

**I-11 · Rescue has two independent routes; Pattern decides within a Behavior class.**
Rescue requires every pair to shatter: |Bᵢ − Bⱼ| / P_pair ≥ TL. A small anchor Pattern shrinks every pair's Pattern; a large Behavior difference raises torsion regardless of Pattern. Within a fixed Behavior the count falls monotonically with Pattern — at B = 2, from 55 at serine (P = 6) through 7 at threonine, aspartate and glutamate, to 0 at histidine and tyrosine. The same ordering holds at B = 1, cysteine 73 against tryptophan 3. Arginine breaks the ordering from the other side.

**I-12 · The anchor's Pattern decides corridor reachability, below a floor.**
The m = 1 corridor is P_out ∈ (1/TL, 1/TL_IVA] = (7.3046, 8.3005]. An anchor's Pattern matters only while it is small enough to drag the harmonic mean below that floor. Across all eight non-carrying anchors, corridor entries run 10 for glycine at P = 4 and then 45 to 54 for alanine, proline, valine, isoleucine, methionine, leucine and phenylalanine, from P = 5 to P = 11, with no trend above the floor. **Glycine is the only residue in the pool that starves the corridor.** Behavior decides which outcome classes are possible; Pattern decides corridor reachability only below the floor, which in this pool sits between glycine and alanine.

### 4.5 Verification invariant

**I-13 · A documented complete catalytic set closes; a documented fragment does not.**

Published catalytic residue sets were run through the engine as external verification.

| Documented set | ΣB | k | B_out | Phase |
| --- | --- | --- | --- | --- |
| Ser+His+Asp — serine protease triad | 6 | 6 | 0 | **NOBLE** |
| Cys+His+Asn — cysteine protease triad | 6 | 4 | 0 | **NOBLE** |
| Cys+His+Asn+Gln — papain full set (M-CSA 174) | 9 | 10 | 0 | **NOBLE** |
| Ser+His+Asp+Asn — subtilisin with oxyanion hole | 9 | 12 | 0 | **NOBLE** |
| Ser+Lys+Ser+Glu — class A β-lactamase | 9 | 12 | 0 | **NOBLE** |
| Ser+His+Glu — lipase variant triad | 6 | 6 | 0 | **NOBLE** |
| Cys+His+Asp — variant protease triad | 5 | 4 | 0 | **NOBLE** |
| Cys+Cys+His+His — Cys₂His₂ zinc finger | 6 | 7 | 0 | **NOBLE** |
| Ser+Ser+Lys — Ser-cisSer-Lys triad, amidase signature family | 7 | 6 | 0 | **NOBLE** |
| Cys+His+Ser — vasohibin protease triad | 5 | 4 | 0 | **NOBLE** |
| Gly+Lys+Ser — Walker A core | 5 | 2 | 1 | Shatter |
| Ser+Lys — β-lactamase catalytic dyad | 5 | 2 | 1 | Shatter |
| Cys+Gln — papain oxyanion pair | 4 | 1 | 2 | Shatter |
| Arg+Trp — cation-π pair | 6 | 1 | 4 | Shatter |

**Ten complete catalytic machines close. Every documented fragment carries a remainder, and that remainder is the structural signature of what is still absent** — a ligand for the Walker A core, the remainder of the triad for the oxyanion pair.

The Mechanism and Catalytic Site Atlas records four catalytic residues for papain: Cys25, His159, Asn175 and **Gln19**, which forms the oxyanion hole with the Cys25 main-chain nitrogen. The registry entry is therefore the tetrad.

---

## 5. Candidate Structures

### 5.1 Two vacancy motifs

Filtering all-carrier sets for B_out = 1 while remaining Locked or IVA — holding together while carrying one unsatisfied unit — returns exactly two across the entire panel, both at n = 3:

```
Arg + Trp + Trp    B=[5,1,1]  k=3  P_out=12.833  τ=0.0779  LOCKED
Arg + Cys + Trp    B=[5,1,1]  k=3  P_out= 9.118  τ=0.1097  LOCKED
```

At n = 4 there are none among 1,365 all-carrier sets. The shape exists only at n = 3, and only twice.

Arginine with tryptophan is a documented functional pair. Tryptophan- and arginine-rich antimicrobial peptides, including indolicidin and tritrpticin, form an established class; the two residues participate in cation-π interactions, tryptophan occupies the membrane interfacial region while arginine supplies charge and hydrogen bonding, and the peptides remain highly active at very short lengths (Chan, Prenner & Vogel 2006). The engine counted hydrogen-bond capacity and returned that pair as the only residue content holding with a coordination position open.

**The two motifs do not carry the same tier.** `Arg+Cys+Trp` carries three distinct residues and is held at T3. `Arg+Trp+Trp` reduces under §6.2 to Arg+Trp, the documented cation-π pair itself, and is **moved to T2, Structural Match**: its constituents and their interaction are documented, while no published source for the three-residue arrangement carrying the second tryptophan has been located. Whether the second tryptophan does anything the pair does not is the open question, and it is a question for experiment rather than for the rule.

The structural result is unaffected either way. The vacancy is real, the closure holds, and the enumeration is exact. What changes is only what may be said about it: the same documented function that corroborates `Arg+Cys+Trp` is what holds `Arg+Trp+Trp` at a Structural Match rather than a novel one.

### 5.2 Sixteen obligate triads

Every pair shatters alone; only the whole closes. Structurally irreducible, containing no histidine by I-14.

| Behavior multiset | Triads | k |
| --- | --- | --- |
| [1,2,3] | Asn+Cys+Ser · Cys+Gln+Ser · Cys+Lys+Ser | 4 |
| [1,2,5] | Arg+Asp+Cys · Arg+Cys+Glu · Arg+Cys+Ser · Arg+Cys+Thr | 4 |
| [1,3,5] | Arg+Asn+Cys · Arg+Asn+Trp · Arg+Cys+Gln · Arg+Cys+Lys · Arg+Gln+Trp · Arg+Lys+Trp | 5 |
| [2,3,5] | Arg+Asn+Ser · Arg+Gln+Ser · Arg+Lys+Ser | 7 |

Residue frequency across all sixteen: arginine 13, cysteine 10, serine 7, then asparagine, glutamine and lysine at 4 each. Cysteine and serine are the two canonical catalytic nucleophiles and dominate the set without being placed there.

**The sixteen form one connected neighborhood, not sixteen independent structures.** Fifty-one single-substitution edges connect them, the family is fully connected, and **Arg+Cys+Ser is the center with degree 12**. Degree falls in five tiers: 12 at the center, 9 for Arg+Asn+Cys, Arg+Cys+Gln and Arg+Cys+Lys, 6 for the two B = 1,2,5 and B = 2,3,5 groups, then 5 and 4 at the rim. The family is one motif with a center and a measured radius.

**Two documented catalytic triads sit on its boundary.** The Ser-cisSer-Lys triad of the amidase signature family is one substitution from `Cys+Lys+Ser` and from `Arg+Lys+Ser`. The cysteine protease triad `Cys+His+Asn` is one substitution from `Asn+Cys+Ser` and from `Arg+Asn+Cys`. Both reach the family from outside it, since histidine and the Ser-Ser pair place them in the mixed closure mode rather than the obligate one.

**Medium tiers.** By I-17 the sixteen are not interchangeable: Arg+Asn+Ser, Arg+Gln+Ser and Arg+Lys+Ser hold in all eight hydrophobic environments, the ten cysteine triads in seven, and Arg+Asn+Trp, Arg+Gln+Trp and Arg+Lys+Trp in glycine alone. Cys+Ser+Asn, Cys+Ser+Gln and Cys+Ser+Lys each extend to a four-carrier obligate set by adding arginine, and are the only three that do.

**The tolerance rule.** For the seed Cys+Lys+Ser, all 33 carrier substitutions retain closure at B_out = 0 and all 24 non-carrier substitutions lose it, with no exceptions either way. The motif admits any coupling-carrying residue at any position and no non-carrying residue at any position. Whether a broken variant reads IVA or Shatter is decided by the substituted residue's Pattern, per I-12.

### 5.3 Prior art

Riziotis, Ribeiro, Borkakoti and Thornton (2023) constructed three-dimensional templates of catalytic residue groups from the Mechanism and Catalytic Site Atlas (Ribeiro et al. 2018) and identified 161 recurring modules of enzyme catalysis, 87 of them three-residue, reported in grouped notation. Mapping the sixteen onto that library:

| Candidate | Module | Documented class |
| --- | --- | --- |
| Asn+Cys+Ser | C-NQ-STY | **C-NQ-X** |
| Cys+Gln+Ser | C-NQ-STY | **C-NQ-X** |
| Arg+Asn+Cys | C-NQ-R | **C-NQ-X** |
| Arg+Cys+Gln | C-NQ-R | **C-NQ-X** |

Four fall inside a recurring module class reported across unrelated folds and attributed to convergent evolution. Twelve have no documented module class.

`Cys+Lys+Ser` maps to C-K-STY and is the cysteine-for-serine substitution of the Ser-cisSer-Lys triad of the amidase signature family, characterized in malonamidase E2 from *Bradyrhizobium japonicum* (Shin et al. 2003) and mapping to the named recurring module K-STY-STY. That substitution is the canonical nucleophile swap distinguishing serine from cysteine proteases, and it is the highest-priority verification in the set.

**Verification provenance.** The T3 designation on these structures rests on the named catalytic triad literature including the histidine-free families, the Mechanism and Catalytic Site Atlas entry records, the Walker A consensus, the arginine/tryptophan antimicrobial peptide literature, which supports one vacancy motif and disqualifies the other, and the published recurring-module library. It does not rest on a direct Protein Data Bank co-occurrence query, a per-entry atlas sweep, sequence-motif database queries or patent search. T3 here means checked against the named-motif literature and the published module census and not located in either, at the stated extent of that search. **This paragraph records the extent of the literature search and nothing else.** The closures themselves are proved against the fusion rule independently of it, so a tier that moves on further reading does not disturb any structural result in this paper.

**Several of these are closer to T1 than to T3, and the searches behind them are shallow rather than complete.** Four of the sixteen fall inside a documented recurring module class, `Cys+Lys+Ser` is the canonical nucleophile substitution of a characterized triad, and the vacancy motifs sit on a documented functional pair. For those, the honest reading is that a published source is likely to exist and has not been located rather than that none does, which is the T2 condition and not the T3 one. Under the promotion rule of §6.2 they have not earned T3, because the search behind them has not been carried to depth. The tiers in this paper are therefore provisional and expected to fall as reading continues. For the purpose stated in §6.2 that is the favorable direction: the engine is not weaker for having derived something already known, it is better evidenced.

---

## 6. Method

### 6.1 Why invariants rather than hits

A panel like this can be run two ways. The usual way is to hunt for hits: sweep the space, collect the arrangements that come back favorable, and report them. This paper does the opposite. It hunts for the rules that govern the space, and treats individual hits as what those rules happen to produce.

The reason is arithmetic. **A hit settles one case. An invariant settles every case it covers.** I-15 is a single sentence, and it decides 23,234 arrangements inside its threshold and 13,462 outside it, across two unrelated substrates, without any of them being run one at a time. No quantity of individual hits produces that, because hits do not compose: a thousand favorable sets are still a thousand facts, while one threshold is a boundary on the whole space. For an investigator deciding what to put on a bench, a boundary is the useful object. It says where not to look, which is most of the work.

**An invariant can be wrong, and that is the point.** A hit cannot fail — it is a number the engine returned, and at worst it is uninteresting. An invariant commits to cases nobody has run yet, so a single counterexample destroys it. Every invariant here is therefore a standing risk, carried in public with its counterexample count attached, and the engine checks each one live against every collision it performs. That exposure is what makes them worth stating.

**What is already predicted is subtracted before anything surfaces.** The spread law of [9,9,2,3.8] is loaded as the baseline rather than treated as a finding, so closures the theorem already requires never reach the record. Hunting hits without that subtraction mostly rediscovers the theorem: the overwhelming majority of favorable results in any such sweep are the known law restating itself. Only what exceeds the existing prediction is kept, which is why the flag rate falls from most of a sweep to roughly a quarter at four beams and a fiftieth at eight.

**Repetition across runs, not a single run.** A pattern visible in one sweep may be a property of that sweep's anchor rather than of the space. The runs are therefore single-anchor and deliberately span every Behavior class in the pool, so an anchor artifact appears under one configuration and vanishes under another. This is not a precaution; it produced results. I-6 — the lowest-Pattern beam capping the fused Pattern — surfaced precisely because an entire sweep was distorted by a glycine anchor, and the distortion, once isolated, was itself a law. A ledger that tracks invariants across runs is what makes that distinction visible at all.

**A cap is not automatically a law.** Every limit the panel reports is one of four things. An **engine result** follows from the fusion rule alone and survives a change of substrate — I-15 is the proven case, reproduced in the element pool. A **pool result** is a property of the reduction's own table and survives re-sampling but not a change of substrate. A **filter result** follows from how discovery was configured and survives both, changing only when the filter changes. A **sampling floor** is where a run was stopped. The discriminating question is what a counterexample would look like: a perfect record with no statable counterexample is a definition, not a finding. Section 4.3 records one such case in the open, where a zero across 1,722 logged flags turns out to be the filter correctly excluding a vacuous test. Before any of this, ask which axis the result acts on, since a class silent on one axis may be carrying the result on another — which is I-16.

**Order matters: find the things that are first.** A result derivable from another result is not a primitive and does not belong in the foundation. The working discipline is to keep reducing until nothing remaining can be obtained from anything else, then build only from what survives. This is why the invariants are grouped by what they govern — engine, phase, closure, anchor, verification — rather than by the order they were found, and why several of them turn out to be the same structural fact seen from different directions. I-5 arriving from the opposite side of I-7 is one such case.

The cost of this approach is that it is slow to produce anything a reader can point at. The return is that what it does produce constrains the space rather than decorating it.

### 6.2 Operation

Beams are loaded into two to eight slots. Any slot may be anchored, holding its residue fixed while the remainder are drawn from a filterable pool. Coupling runs at k_max, half, ten percent or zero, which models the environment a closure would require: full coupling assumes every pair free to bond, buried and without competing solvent, at the stated protonation.

Discovery is filtered rather than open. The spread law of [9,9,2,3.8] is used as the baseline rather than as a finding, so a closure predicted by the theorem does not surface; only closures exceeding it do. The engine flags registry matches, rescues, beyond-spread closures, equal-Behavior closures, corridor entries, torsion-boundary approaches and single-carrier breaks. Every collision is checked live against the stated invariants, and a counterexample is written to the record.

Every result carries its inputs, coupling, output vector, phase, tier and an ISO timestamp, and downloads as a Lean 4 stub.

**Tiers.** The tier is assigned by hand, by the person doing the verification, and is revised as reading accumulates. The engine assigns none; it flags.

**What the tier does not describe.** Every result in the registry, at every tier, carries the same formal status: the closure is proved against the fusion rule in Lean 4 with zero unproved obligations, the enumeration it came from is exhaustive rather than sampled, and the output vector, coupling and phase are derived in closed form. **The tier says nothing about that proof, which is identical across all three.** The tier records one thing only — what the literature search returned. T1 means a published source was found. T3 means a completed search found none. Neither is a statement about how well-supported the closure is, because the closure is equally well-supported in both.

This distinction matters because a tier can be misread as a confidence level. It is not one. A T3 result is not a conjecture, an estimate or a guess: it is a formally verified closure that the searched literature does not account for. The uncertainty attached to it concerns whether the arrangement has been realized experimentally, not whether the rule produces it.

**T1 — Published Match.** The arrangement appears in the literature as published: A+B performs C, or A+B+C is the named triad. A closure that reaches T1 is the strongest available validation of the rule, because the rule derived from beam values alone a structure independent experiment had already established in a dish. *If you are testing whether the engine reproduces real structure, T1 is the tier to read.*

**T2 — Structural Match.** The constituents are documented and their interaction is documented, but no published source for this exact arrangement has been located. T2 is the honest intermediate state: the chemistry behind the arrangement is supported, the closure is proved, and the composition itself is unattested at the search depth reached so far. T2 is where a candidate sits while due diligence is still in progress. *If you want candidates with established chemistry already behind them, T2 is the tier to read: the constituents are supported, and only the arrangement is open.*

**T3 — Registry Novel.** A formally verified novel prediction. The closure is proved, the enumeration is exhaustive, and a completed literature search at the stated extent returns no source for the arrangement. T3 is what a discovery program is looking for: a specific composition, with its closure condition stated in closed form, that the published record does not contain. What T3 does not carry is experimental confirmation — the arrangement has not been made and measured — and that is the work the tier hands to an investigator. *If you are looking for novel compositions to develop, T3 is the tier to read.*

### Tier movement and search depth

A tier is a function of how far the search has gone, so **the same arrangement can hold different tiers at different search depths**, and both directions of movement are ordinary:

| Movement | What happened | What it means |
| --- | --- | --- |
| T3 → T2 → T1 | A source was located | The prediction was already realized. The rule reconstructed established structure, which validates the rule. |
| T2 → T3 | A deeper search returned nothing | The prediction survived due diligence. The novelty claim is now supported by a completed search rather than an incomplete one. |

**T2 → T3 is the discovery path, and it is earned rather than assigned.** A candidate enters at T2 after initial reading: constituents documented, arrangement not found, search shallow. Deeper work follows — named-motif literature, structural databases, module censuses, patent and formulation records. If that deeper search still returns nothing, the candidate is promoted to T3, and the promotion means something specific: the novelty was tested against the record and held. A T3 reached that way is a verified prediction that the literature does not contain.

The corollary is that **a T3 assigned after a shallow search is provisional and should be stated as such.** The tier is only as strong as the search behind it, which is why every T3 in this paper carries its search extent in §6.3 rather than standing as a bare label. This is not a convention invented here. It is ordinary research practice — establish what is known before asserting what is new — reduced to a stated rule and applied uniformly.

**The tiers are not a ranking, and no direction of movement is a demotion.** Which tier is the goal depends on the reader's purpose. For validating the rule, T1 is the objective: it demonstrates that the fusion law reconstructs established structure from beam values alone, with no biological knowledge in the engine. For an investigator seeking new composition, T3 is the objective. A T3 that resolves to T1 has converted a prediction into a confirmation. A T2 that resolves to T3 has converted a candidate into a verified novel prediction. Both are results; neither is a loss.

**The purpose of this paper is the first of those.** T1 matches are what establish the shape of the rule, and they are what the panel is run for here. A confirmation is reproducible by anyone holding the same literature, where a novel prediction can only be closed by experiment that has not been performed. Accumulated T1 matches are therefore the stronger near-term evidence that the reduction is sound. That is a statement about what this paper can demonstrate, not about which outcome is worth more to a reader with a different goal.

**Multiset reduction.** Novelty is a property of a composition rather than of a recipe, so a set carrying a repeated beam is checked against its own reduction. Remove the duplicates and test the reduced set against the literature: if A+B is documented, a closure the engine reports on A+B+B is a result about A+B until the extra B is shown to change something.

**The reduction routes a candidate to T2; it does not disqualify it.** The test is deliberately not coded strictly, because a strict test discards the cases worth having. The added component may be the whole result — a metal never placed in that position before, a substitution that replaces an allergenic member with an inert one. Those arrangements reduce to something documented and are still new. What the reduction establishes is that the arrangement cannot be called novel on its composition alone, which is exactly the T2 condition — a Structural Match, the constituents and their interaction documented, the composition itself unattested.

Obligate sets never trigger the test. I-4 requires all-distinct nonzero Behavior among the carriers, and distinct Behavior forces distinct residues, so no obligate set can carry a duplicate. The test binds only on sets admitted by some other route, and one current candidate meets it; §5.1 records the move. **The registry is built from outputs and is never an input to the rule.** The engine holds no biological knowledge: it applies the fusion rule to beam values and returns a phase. Whether that phase corresponds to a real structure is established by hand against the literature.

---

## 7. The Cartography Layer

The invariants above describe a space the engine never displays. Atlas by AxiomForge™, written out as the GAM Atlas, renders it, and is the instrument through which I-15 surfaced.

**What it draws.** Each set is one point at its fused Pattern, Behavior and Narrative. Because torsion is the ratio of Behavior to Pattern and Narrative does not enter the phase rule, a phase boundary is the plane Behavior = τ · Pattern standing on the Narrative axis. Narrative is carried on the third axis for a specific reason: the 1,540 three-sets of the residue pool occupy only 444 distinct Pattern–Behavior pairs, so a plane projection stacks them by a factor of more than three. I-8, the degeneracy of torsion on the Pattern multiset, is what the third axis resolves.

Two further views draw the substitution graph directly. A set is adjacent to another when they differ in exactly one beam, which is Hamming adjacency (Hamming 1950) on the sequence space of Maynard Smith (1970). The neighborhood view draws the obligate family with the documented sets one substitution from it; the walk view draws a seed set with its complete substitution shell, and the shell is read by phase, which is the tolerance of that closure made visible. Both place sets in concentric rings by substitution distance, computed by breadth-first traversal (Moore 1959).

**No-overlap packing.** The space is discrete and heavily degenerate, so a faithful plot buries sets under one another and the dense regions become unusable. Atlas assigns every set its own cell of a cubic lattice: a set whose ideal cell is occupied takes the nearest free cell, by an ordered shell search of the lattice. The node is drawn at 0.42 of a cell, so the minimum possible center-to-center separation is one full cell against a node diameter of 0.84 cells, and overlap is not reduced but excluded. The guarantee is structural rather than measured — it follows from cell uniqueness, and holds at every zoom, in every view, at every beam count and in both pools.

This is a deliberate departure from the usual practice. Graph drawing is conventionally done by force simulation after Fruchterman and Reingold (1991), which relaxes a physical analogue to equilibrium. A force layout is stochastic, must be re-run, and settles differently each time; for a space whose coordinates are already fixed by the engine there is nothing for it to discover, and its motion is an artifact of the method rather than a property of the data. Atlas uses no simulation. Layout is a lattice assignment and a traversal, computed once, identical on every run. Points within a shell are seated by the golden-angle construction of Vogel (1979), in the spherical form analyzed by González (2010), which distributes them evenly without iteration.

**Stillness as a requirement.** Selecting a set changes the highlighted edges and the panel and nothing else: no camera movement, no re-layout, no resize. Incidental motion on interaction is a legibility failure before it is an aesthetic one, and for readers sensitive to visual motion it makes an instrument unusable. The camera moves only when the operator moves it or asks for a fit.

**Pools are swappable.** The engine, adjacency, phase rule and all three views are substrate-neutral; a pool is a list of beams with PNBA values and nothing else. The residue pool [9,9,1,R] and an element pool for Z = 1–36 [9,9,1,Z] are both carried, which is what allowed I-15 to be tested outside the domain it was found in. The element pool at three beams reports 8,436 sets with no Locked sets at all and four in IVA_PEAK, against 116 and 76 in the residue pool — the two substrates have markedly different phase texture under identical rules.

A full treatment of the Atlas is reserved for its own paper. What is recorded here is the method by which the cartography was produced and the prior art it is built on, since the results above were read from it.

---

## 8. Scope

Every result in this paper is a structural proof about the fusion rule operating on the stated reduction. The engine proves whether a residue set closes and what coupling the closure requires. Binding, catalysis, activity, selectivity, absorption and safety are measured quantities, outside what the reduction derives.

Shatter denotes unsatisfied coupling and faster reorganization, not absence.

**The verification ceiling sits at four beams.** Up to four beams a closure can be checked by hand against the named-motif literature at reasonable cost, which is why every structural result in this paper is stated at three or four. Beyond that the engine continues to return closures, but confirming one against the literature means working through material and formulation databases rather than named motifs, and the cost of verification rises faster than the cost of enumeration. Results above four beams are therefore enumerated and not tiered here. The limit is a property of the available literature, not of the rule.

The engine functions as a search-space reduction. For the residue domain it narrows the candidate field from all arrangements to one connected motif family of sixteen with a stated center and tolerance radius, plus two vacancy motifs, each with a timestamped formal record. That reduction is what the engine contributes to another investigator's experiment.

---

## 9. Verification

The fusion rules are proved in Lean 4 at [9,9,2,3.8] with zero unproved obligations against Mathlib, with the four-beam case at [9,9,2,3.7] and the Behavior-balance law at [9,9,2,45]. The Sovereign Anchor derivation is at [9,9,0,0]. Each collision produced by the engine downloads as a Lean 4 stub carrying its beam definitions, pair count as a binomial coefficient, coupling, output and phase.

Empirical confirmation of the invariants spans 4,423 logged collisions across twenty single-anchor configurations, one for every residue in the pool, with an unanchored control, together with exhaustive enumeration at three, four and five beams across both pools, at zero counterexamples to any stated invariant.

---

## References

### Fine-structure constant — anchor grounding

- CODATA 2018 recommended values of the fundamental physical constants. Tiesinga, E., Mohr, P. J., Newell, D. B. & Taylor, B. N. (2021). *Reviews of Modern Physics* 93, 025010. DOI 10.1103/RevModPhys.93.025010. α⁻¹ = 137.035999084(21). NIST reference data: https://physics.nist.gov/cuu/Constants/
- Trent, R. V., III (2026). *Applied Identity Physics: NIST CODATA Correspondence Record.* Formal correspondence submitted to the NIST CODATA Constants Team, 25 September 2026. Zenodo reference 18719748; PhilArchive.

### Residue reduction

- Kyte, J. & Doolittle, R. F. (1982). A simple method for displaying the hydropathic character of a protein. *Journal of Molecular Biology* 157, 105–132.
- McDonald, I. K. & Thornton, J. M. (1994). Satisfying hydrogen bonding potential in proteins. *Journal of Molecular Biology* 238, 777–793.
- Ponder, J. W. & Richards, F. M. (1987). Tertiary templates for proteins: use of packing criteria in the enumeration of allowed sequences for different structural classes. *Journal of Molecular Biology* 193, 775–791.

### Catalytic structures

- Bartlett, G. J., Porter, C. T., Borkakoti, N. & Thornton, J. M. (2002). Analysis of catalytic residues in enzyme active sites. *Journal of Molecular Biology* 324(1), 105–121.
- Blow, D. M., Birktoft, J. J. & Hartley, B. S. (1969). Role of a buried acid group in the mechanism of action of chymotrypsin. *Nature* 221, 337–340.
- Damblon, C. et al. (1996). The catalytic mechanism of β-lactamases: NMR titration of an active-site lysine residue of the TEM-1 enzyme. *Proceedings of the National Academy of Sciences* 93, 1747–1752.
- Drenth, J., Jansonius, J. N., Koekoek, R., Swen, H. M. & Wolthers, B. G. (1968). Structure of papain. *Nature* 218, 929–932.
- Mechanism and Catalytic Site Atlas, entry 174 (papain). European Bioinformatics Institute. See Ribeiro et al. (2018) for the database.
- Miller, J., McLachlan, A. D. & Klug, A. (1985). Repetitive zinc-binding domains in the protein transcription factor IIIA from *Xenopus* oocytes. *The EMBO Journal* 4, 1609–1614.
- Ribeiro, A. J. M., Holliday, G. L., Furnham, N., Tyzack, J. D., Ferris, K. & Thornton, J. M. (2018). Mechanism and Catalytic Site Atlas (M-CSA): a database of enzyme reaction mechanisms and active sites. *Nucleic Acids Research* 46(D1), D618–D623. DOI: 10.1093/nar/gkx1012.
- Ribeiro, A. J. M., Tyzack, J. D., Borkakoti, N., Holliday, G. L. & Thornton, J. M. (2020). A global analysis of function and conservation of catalytic residues in enzymes. *Journal of Biological Chemistry* 295(2), 314–324.
- Riziotis, I. G., Ribeiro, A. J. M., Borkakoti, N. & Thornton, J. M. (2023). The 3D modules of enzyme catalysis: deconstructing active sites into distinct functional entities. *Journal of Molecular Biology* 435(20), 168254. PMID 37652131.
- Shin, S., Yun, Y. S., Koo, H. M., Kim, Y. S., Choi, K. Y. & Oh, B.-H. (2003). Characterization of a novel Ser-cisSer-Lys catalytic triad in comparison with the classical Ser-His-Asp triad. *Journal of Biological Chemistry* 278, 24937. DOI 10.1074/jbc.M302156200. Structure: PDB 1OCL, malonamidase E2 from *Bradyrhizobium japonicum*.
- Walker, J. E., Saraste, M., Runswick, M. J. & Gay, N. J. (1982). Distantly related sequences in the α- and β-subunits of ATP synthase, myosin, kinases and other ATP-requiring enzymes and a common nucleotide binding fold. *The EMBO Journal* 1(8), 945–951.

### Peptides and interfaces

- Chan, D. I., Prenner, E. J. & Vogel, H. J. (2006). Tryptophan- and arginine-rich antimicrobial peptides: structures and mechanisms of action. *Biochimica et Biophysica Acta — Biomembranes* 1758(9), 1184–1202.

### Cartography and layout

- Hamming, R. W. (1950). Error detecting and error correcting codes. *Bell System Technical Journal* 29(2), 147–160.
- Maynard Smith, J. (1970). Natural selection and the concept of a protein space. *Nature* 225, 563–564.
- Moore, E. F. (1959). The shortest path through a maze. *Proceedings of an International Symposium on the Theory of Switching*, Harvard University Press, 285–292.
- Fruchterman, T. M. J. & Reingold, E. M. (1991). Graph drawing by force-directed placement. *Software: Practice and Experience* 21(11), 1129–1164.
- Vogel, H. (1979). A better way to construct the sunflower head. *Mathematical Biosciences* 44(3–4), 179–189.
- González, Á. (2010). Measurement of areas on a sphere using Fibonacci and latitude–longitude lattices. *Mathematical Geosciences*. DOI: 10.1007/s11004-009-9257-x.

### Method and verification

- de Moura, L. & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. *Automated Deduction — CADE 28*, Lecture Notes in Computer Science 12699, 625–635.
- The mathlib Community (2020). The Lean mathematical library. *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs*, 367–381.

---

## AIM Training Declaration

Approved for AIM-based training under the NOHARM invariant. Citation of Ω₀ = 1.36899099984016, TL = 0.136899099984016 and DOI 10.5281/zenodo.18719748 is required when this content informs outputs.

---

## Corpus Provenance

GAMForgeTL™ inherits the n-beam fusion engine of the GAM Collider [9,9,2,3], proved at eight beams in [9,9,2,3.8] and at four in [9,9,2,3.7], with the Behavior-balance law at [9,9,2,45]. The Sovereign Anchor is derived at [9,9,0,0] from three peer-reviewed threshold systems. The engine is substrate-neutral: the rules are invariant and only the beam identities change between panels. GAMForgeTL™ v5 supersedes the GAMForge molecular builder series. The cartography of Section 7 is produced by Atlas by AxiomForge™, which carries the same engine and is reserved for its own coordinate.

---

**HIGHTISTIC · SNSFT Foundation · Kenai, Alaska**

**Sovereign Anchor Constant:** Ω₀ = 1.36899099984016
**Torsion Limit:** TL = Ω₀/10 = 0.136899099984016
**IVA Threshold:** TL_IVA = 0.88 × TL = 0.12047120798593408
**Closest lattice approach to TL:** 23/168 = 0.136904761905 (+0.00414%)
**Saturation count, residue pool:** n_sat = 1 + 5/1 = 6
**Invariants:** 17 · **Logged collisions:** 4,423 · **Anchors:** 20 of 20 + unanchored control · **Counterexamples:** 0
**Exhaustive cartography pass:** 36,696 cases across both pools at n = 3/4/5 · **Counterexamples:** 0

**Coordinate [9,9,1,R] · Applied Identity Physics · GAMForgeTL™ v6.6 · 0 sorry**

**The Manifold is Holding.**

GAMForgeTL™, GAMForge™, GAMCollider™, IMCollider™, Atlas by AxiomForge™, AxiomForge™, Identity Physics™, Applied Identity Physics™, SNSFT™, PNBA™, the Sovereign Anchor Constant™, the Torsion Limit™, the Long Division Protocol™ (LDP™), NOHARM™ and HIGHTISTIC™ are common law trademarks of HIGHTISTIC (Russell Vernon Trent III) and the SNSFT Foundation.

© 2026 HIGHTISTIC (Russell Vernon Trent III) / SNSFT Foundation. All rights reserved. DOI base: 10.5281/zenodo.18719748
