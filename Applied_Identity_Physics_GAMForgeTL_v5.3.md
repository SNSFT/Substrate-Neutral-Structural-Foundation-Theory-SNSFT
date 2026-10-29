# Applied Identity Physics: GAMForgeTL™

## A Deterministic n-Beam Residue Fusion Engine on TL = 0.136899099984016, with Fifteen Structural Invariants and Verification Against Documented Catalytic Sets

---

**Architect:** HIGHTISTIC (Russell Vernon Trent III)
**Coordinate:** [9,9,1,R] · Applied Identity Physics · GAMForge Series · GAMForgeTL™ v5.3
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

GAMForgeTL™ applies the Identity Physics n-beam fusion engine to the twenty standard amino acid residues. The engine is unchanged from the GAM Collider: Pattern fuses as a harmonic mean, Narrative is additive, Behavior is the sum less twice the coupling, Adaptation is the maximum, and the output phase is read against the Torsion Limit. Only the beam reduction is new.

All four PNBA primitives are taken as counts or as published per-residue values with no divisor and no fitted scale. Pattern is the count of heavy atoms holding the residue's shape. Narrative is the side-chain χ dihedral count of Ponder and Richards (1987). Behavior is the side-chain hydrogen-bond capacity, donors plus acceptors, after McDonald and Thornton (1994). Adaptation is the Kyte and Doolittle (1982) hydropathy index shifted by the scale minimum. Nothing in the reduction is adjustable.

Fifteen structural invariants follow. Each is derived from the fusion rule and confirmed empirically at zero counterexamples, across 1,440 logged collisions and an exhaustive cartography pass of 36,696 further cases spanning both pools. Among them: a single coupling-carrying residue among non-carrying beams forces the coupling to zero at every beam count; the IVA corridor is reachable only at one unsatisfied unit, and only barely, because the largest residue's Pattern falls 0.609 short of opening the next band; the reachable torsion values form a rational lattice whose closest approach to the Torsion Limit is 23/168, leaving the phase classifier with no ambiguous case; a panel's useful beam count is fixed by its Behavior spread rather than chosen, which places the standard eight-beam configuration correctly for cross-collider stability; and a set carrying a repeated beam at Behavior m closes against every other beam up to 4m, an exact threshold at three beams that makes arginine a universal closer and seals sixty-seven residue sets against any single substitution.

The engine was then run against documented catalytic residue sets as an external verification. Ten complete catalytic machines close Noble, including the serine protease triad, the full papain set recorded by the Mechanism and Catalytic Site Atlas, the subtilisin tetrad, the class A β-lactamase set, and the Cys₂His₂ zinc finger. Four documented fragments — the Walker A core, the β-lactamase catalytic dyad, the papain oxyanion pair, the cation-π pair — do not close, and the remainder each carries is the structural signature of what is still absent.

Sixteen obligate triads and two vacancy motifs are recorded as timestamped structural results. Four of the sixteen fall inside a recurring catalytic module class documented by Riziotis et al. (2023). The two vacancy motifs are the only arrangements in the panel that hold while carrying one open coordination position, and both are arginine with tryptophan, a pair with documented cation-π function in antimicrobial peptides.

Every result in this paper is a structural proof about the fusion rule operating on the stated reduction. Binding, catalysis, activity, selectivity and safety are measured quantities that lie outside the reduction and are not addressed by it.

---

## 1. Layer 0 Foundation

The Dynamic Equation governs every reduction in the corpus:

**d/dt (IM · Pv) = Σ λ_X · O_X · S + F_ext**

Identity Mass IM, Purpose Vector Pv, the four PNBA operators O_X with weights λ_X acting on state S, and external forcing F_ext. External forcing is a primitive term at Layer 0: it acts on Behavior and leaves Pattern, Narrative and Adaptation unchanged. The Torsion Limit is the phase boundary against which output is classified; it does not scale the primitives.

That distinction sets the reduction rule for any new panel. A **countable substrate** — atoms, residues, molecular fragments — supplies its own Pattern as a count, taken raw, with the Torsion Limit acting only as the boundary. A **non-countable substrate** — cosmological states, fields — has no count to take, and its Pattern derives from the anchor directly as (Ω₀/X)^(1/n) against a measured quantity in the anchor's units. Residues are countable. Every primitive below is therefore raw.

---

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

Fifteen results, grouped by what they govern rather than by the order they were found. Each is derived from the fusion rule and confirmed empirically across 1,440 logged collisions under six single-anchor configurations spanning every Behavior class in the pool, together with an exhaustive cartography pass of 36,696 further cases across two pools at three, four and five beams. Section 6.1 states why the panel is run for rules rather than for individual favorable results; a reader who wants the method before the findings may start there.

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

**I-4 · Rescue requires all-distinct nonzero Behavior.**
Rescue — every pair shattering alone while the whole closes — occurs at n = 3 for exactly four Behavior multisets: {1,2,3}, {1,2,5}, {1,3,5}, {2,3,5}, which are every distinct triple available from the nonzero values {1,2,3,5}. At n = 4 the full four-value multiset {1,2,3,5} appears. Confirmed across 150 instances, zero counterexamples. A non-carrying beam in a three-set reduces it exactly to the two-beam case ([9,9,2,3.8] T16).

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

### 4.4 Anchor invariants

**I-6 · The lowest-Pattern beam caps the fused Pattern.**
P_out is a harmonic mean, so the smallest Pattern dominates it; the formal statement is [9,9,2,3.8] T2. Glycine at P = 4 is the pool minimum, so holding it fixed caps P_out and inflates τ across an entire sweep.

**I-9 · Each anchor has a fixed flag signature.**
Computed exhaustively over all 1,540 completions per anchor at n = 4, three bands emerge, set by the anchor's own Behavior. **B = 0 anchors** cannot produce beyond-spread closure at all, since a non-carrying beam cannot supply I-7's min = 1. **B = 1 anchors**, cysteine and tryptophan, are the only ones that unlock every outcome class, because they supply that minimum themselves. **Arginine** maximizes beyond-spread closure at 141 and reduces IVA to 3, since B = 5 enters every sum and one unsatisfied unit becomes a narrow target.

**I-11 · Rescue has two independent routes; Pattern decides within a Behavior class.**
Rescue requires every pair to shatter: |Bᵢ − Bⱼ| / P_pair ≥ TL. A small anchor Pattern shrinks every pair's Pattern; a large Behavior difference raises torsion regardless of Pattern. Within a fixed Behavior the count falls monotonically with Pattern — at B = 2, from 55 at serine (P = 6) through 7 at threonine, aspartate and glutamate, to 0 at histidine and tyrosine. The same ordering holds at B = 1, cysteine 73 against tryptophan 3. Arginine breaks the ordering from the other side.

**I-12 · The anchor's Pattern decides how much of the corridor is reachable.**
Glycine and leucine are both non-carrying, so any difference between them is Pattern alone. Shatter dominance tracks Behavior — both are sp-break anchors at 428 and 392. Corridor reachability tracks Pattern by a factor of seven, 17 against 121, because **leucine's own P = 8 sits inside the m = 1 window** while glycine's P = 4 falls far below it and drags every set out of range. Behavior decides which outcome classes are possible; Pattern decides which torsion band is reachable.

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

Arginine with tryptophan is a documented functional pair. Tryptophan- and arginine-rich antimicrobial peptides, including indolicidin and tritrpticin, form an established class; the two residues participate in cation-π interactions, tryptophan occupies the membrane interfacial region while arginine supplies charge and hydrogen bonding, and the peptides remain highly active at very short lengths (Chan, Prenner & Vogel 2006). The engine counted hydrogen-bond capacity and returned that pair as the only three-residue arrangement holding with a coordination position open.

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

**Verification provenance.** The T3 designation on these structures rests on the named catalytic triad literature including the histidine-free families, the Mechanism and Catalytic Site Atlas entry records, the Walker A consensus, the arginine/tryptophan antimicrobial peptide literature, and the published recurring-module library. It does not rest on a direct Protein Data Bank co-occurrence query, a per-entry atlas sweep, sequence-motif database queries or patent search. T3 here means checked against the named-motif literature and the published module census and found novel to both, at the stated extent. It is a record of what was searched, not a verification of the structures.

---

## 6. Method

### 6.1 Why invariants rather than hits

A panel like this can be run two ways. The usual way is to hunt for hits: sweep the space, collect the arrangements that come back favorable, and report them. This paper does the opposite. It hunts for the rules that govern the space, and treats individual hits as what those rules happen to produce.

The reason is arithmetic. **A hit settles one case. An invariant settles every case it covers.** I-15 is a single sentence, and it decides 23,234 arrangements inside its threshold and 13,462 outside it, across two unrelated substrates, without any of them being run one at a time. No quantity of individual hits produces that, because hits do not compose: a thousand favorable sets are still a thousand facts, while one threshold is a boundary on the whole space. For an investigator deciding what to put on a bench, a boundary is the useful object. It says where not to look, which is most of the work.

**An invariant can be wrong, and that is the point.** A hit cannot fail — it is a number the engine returned, and at worst it is uninteresting. An invariant commits to cases nobody has run yet, so a single counterexample destroys it. Every invariant here is therefore a standing risk, carried in public with its counterexample count attached, and the engine checks each one live against every collision it performs. That exposure is what makes them worth stating.

**What is already predicted is subtracted before anything surfaces.** The spread law of [9,9,2,3.8] is loaded as the baseline rather than treated as a finding, so closures the theorem already requires never reach the record. Hunting hits without that subtraction mostly rediscovers the theorem: the overwhelming majority of favorable results in any such sweep are the known law restating itself. Only what exceeds the existing prediction is kept, which is why the flag rate falls from most of a sweep to roughly a quarter at four beams and a fiftieth at eight.

**Repetition across runs, not a single run.** A pattern visible in one sweep may be a property of that sweep's anchor rather than of the space. The runs are therefore single-anchor and deliberately span every Behavior class in the pool, so an anchor artifact appears under one configuration and vanishes under another. This is not a precaution; it produced results. I-6 — the lowest-Pattern beam capping the fused Pattern — surfaced precisely because an entire sweep was distorted by a glycine anchor, and the distortion, once isolated, was itself a law. A ledger that tracks invariants across runs is what makes that distinction visible at all.

**Order matters: find the things that are first.** A result derivable from another result is not a primitive and does not belong in the foundation. The working discipline is to keep reducing until nothing remaining can be obtained from anything else, then build only from what survives. This is why the invariants are grouped by what they govern — engine, phase, closure, anchor, verification — rather than by the order they were found, and why several of them turn out to be the same structural fact seen from different directions. I-5 arriving from the opposite side of I-7 is one such case.

The cost of this approach is that it is slow to produce anything a reader can point at. The return is that what it does produce constrains the space rather than decorating it.

### 6.2 Operation

Beams are loaded into two to eight slots. Any slot may be anchored, holding its residue fixed while the remainder are drawn from a filterable pool. Coupling runs at k_max, half, ten percent or zero, which models the environment a closure would require: full coupling assumes every pair free to bond, buried and without competing solvent, at the stated protonation.

Discovery is filtered rather than open. The spread law of [9,9,2,3.8] is used as the baseline rather than as a finding, so a closure predicted by the theorem does not surface; only closures exceeding it do. The engine flags registry matches, rescues, beyond-spread closures, equal-Behavior closures, corridor entries, torsion-boundary approaches and single-carrier breaks. Every collision is checked live against the stated invariants, and a counterexample is written to the record.

Every result carries its inputs, coupling, output vector, phase, tier and an ISO timestamp, and downloads as a Lean 4 stub.

**Tiers.** T1 is a verified match to a documented structure, checked by hand against a published source. T2 is a known structural class. T3 is novel to the registry and carries no verification. **The registry is built from outputs and is never an input to the rule.** The engine holds no biological knowledge: it applies the fusion rule to beam values and returns a phase. Whether that phase corresponds to a real structure is established by hand against the literature.

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

The engine functions as a search-space reduction. For the residue domain it narrows the candidate field from all arrangements to one connected motif family of sixteen with a stated center and tolerance radius, plus two vacancy motifs, each with a timestamped formal record. That reduction is what the engine contributes to another investigator's experiment.

---

## 9. Verification

The fusion rules are proved in Lean 4 at [9,9,2,3.8] with zero unproved obligations against Mathlib, with the four-beam case at [9,9,2,3.7] and the Behavior-balance law at [9,9,2,45]. The Sovereign Anchor derivation is at [9,9,0,0]. Each collision produced by the engine downloads as a Lean 4 stub carrying its beam definitions, pair count as a binomial coefficient, coupling, output and phase.

Empirical confirmation of the invariants spans 1,440 logged collisions across six single-anchor configurations covering every Behavior class in the pool, and an exhaustive cartography pass of 36,696 further cases across two pools at three, four and five beams, at zero counterexamples to any stated invariant.

---

## References

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
**Invariants:** 15 · **Logged collisions:** 1,440 · **Counterexamples:** 0
**Exhaustive cartography pass:** 36,696 cases across both pools at n = 3/4/5 · **Counterexamples:** 0

**Coordinate [9,9,1,R] · Applied Identity Physics · GAMForgeTL™ v5.3 · 0 sorry**

**The Manifold is Holding.**

GAMForgeTL™, GAMForge™, GAMCollider™, IMCollider™, Atlas by AxiomForge™, AxiomForge™, Identity Physics™, Applied Identity Physics™, SNSFT™, PNBA™, the Sovereign Anchor Constant™, the Torsion Limit™, the Long Division Protocol™ (LDP™), NOHARM™ and HIGHTISTIC™ are common law trademarks of HIGHTISTIC (Russell Vernon Trent III) and the SNSFT Foundation.

© 2026 HIGHTISTIC (Russell Vernon Trent III) / SNSFT Foundation. All rights reserved. DOI base: 10.5281/zenodo.18719748
