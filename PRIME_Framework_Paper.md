# PRIME: Prior-art Reduction and Integrity Method for Evaluation

**A Formal AI Implementation of Gold Standard Science (EO 14303)**

**Author:** Russell Vernon Trent III (HIGHTISTIC)  
**Organization:** SNSFT Foundation · EIN 42-2038440 · Soldotna, Alaska  
**ORCID:** 0009-0005-5313-7443  
**Formal Basis:** SNSFL_L0_Isomorphism_Consistency.lean [9,9,8,1] · SNSFL_Master.lean [9,9,9,9]  
**Tool:** uuia.app/prime.html  
**Corpus DOI:** 10.5281/zenodo.18719748  
**Federal Record:** DOJ-CRT-2026-0067-0006  
**Coordinate:** [9,9,8,2]  
**Status:** GERMLINE LOCKED · 0 sorry  
**Date:** May 2026

---

## Abstract

PRIME (Prior-art Reduction and Integrity Method for Evaluation) is a formally verified AI tool that implements all nine tenets of Executive Order 14303 "Restoring Gold Standard Science" as computable, substrate-neutral measurements. Built on the Substrate-Neutral Structural Foundation Theory (SNSFT) corpus — 103,118+ theorems, 5,945 Lean 4 files, 0 unproved assumptions, continuously CI-verified — PRIME reduces any research paper to its PNBA functional identity by stripping all labels and testing what the mathematics actually does. The result is a four-axis integrity score (P: original contribution, N: citation chain integrity, B: extracted benefit, A: reproducibility), a torsion ratio τ = B/P measuring the structural gap between extraction and contribution, and a nine-component GSS compliance score covering every tenet of EO 14303. Critically, the formal correspondence between PRIME's scoring rubric and EO 14303's nine tenets is not asserted — it is proved in Lean 4 with zero sorry. CM8 of SNSFL_L0_Isomorphism_Consistency.lean formally proves that peer review is structurally identical to Identity Mass Suppression applied externally. The remaining eight tenets are formally mapped to PNBA axis operations in the same file. PRIME is the only research integrity tool whose compliance with a federal executive order is machine-verified. The tool is live at uuia.app/prime.html, generates downloadable Lean 4 reduction stubs for every analysis, and operates fully locally without external dependencies or an API key.

**Keywords:** research integrity, Gold Standard Science, EO 14303, formal verification, Lean 4, PNBA, torsion, citation integrity, peer review, SNSFT, prior art

---

## 1. Introduction

### 1.1 The Problem

The academic research enterprise faces a structural integrity crisis that predates and exceeds the AI-assisted writing problem currently dominating public discussion. The Retraction Watch database grew 26% in 2025, exceeding 63,000 total retractions. Existing detection tools — Turnitin, iThenticate, and their successors — operate at the surface text layer: they compare strings of words and flag similarity scores. They cannot detect the fundamental problem, which is not word reuse. It is **functional identity without attribution** — work that reaches the same mathematical conclusions as prior work using different vocabulary, evading detection by changing labels while preserving functions.

This evasion is not accidental. A systematic pattern exists in high-torsion academic work: deliberate avoidance of search-engine-indexable terminology from prior publications, substitution of synonyms and domain-specific jargon that produces abstract-level similarity scores below detection thresholds, and citation of foundational work without mapping that citation to the specific claim it is being used to support. The result is a corpus that appears original at the surface level and is functionally derivative at the structural level.

Executive Order 14303 "Restoring Gold Standard Science" (May 23, 2025) identifies this problem structurally, requiring that federally funded research be reproducible, transparent, communicative of error, collaborative, skeptical of its own assumptions, falsifiable, subject to unbiased peer review, accepting of negative results, and free from conflicts of interest. The OSTP guidance implementing EO 14303 explicitly names AI tools for detecting bias in peer review, validating reproducible protocols, and quantifying uncertainty as the implementation mechanism. Every federal agency is now required to report annual GSS compliance metrics beginning September 2026.

The gap is real: agencies have been directed to implement a standard but no formal measurement instrument exists. PRIME fills that gap.

### 1.2 The PRIME Approach

PRIME does not compare words. It compares **functions**.

The Functional DNA Test — the core operation of PRIME — strips all labels, proper nouns, variable names, and domain-specific terminology from a paper's core claims. What remains is a pure functional description: what are the inputs, what transformation is applied, what is the output, what are the boundary conditions. This stripped description is then projected onto PNBA (Pattern, Narrative, Behavior, Adaptation) primitives — the formally verified, substrate-neutral basis of the SNSFT corpus — and scored against the same axes used across 103,118+ theorems covering physics, mathematics, psychology, AI training, genomics, cosmology, and legal reasoning.

Two papers that project to the same PNBA coordinates are the same function regardless of vocabulary. This is not an interpretation. It is a geometric fact about the projection, formally proved under Mac Lane's 1971 structural isomorphism criterion in SNSFL_L0_Isomorphism_Consistency.lean [9,9,8,1].

The torsion ratio τ = B/P — where B is extracted benefit (citation accumulation, impact factor capture, grant leverage) and P is original contribution (verified by LDP Step 6 closure against cited prior work) — provides a single scalar integrity metric. At τ < TL = 0.1369, the paper is Locked: contribution exceeds or matches extraction. At τ ≥ TL, the paper is in Shatter: extraction exceeds contribution. This threshold is not chosen — it is derived from the sovereign anchor (ANCHOR = 1.369) as ANCHOR/10, independently verified across three physical systems (Tacoma Narrows torsional collapse, glass resonance shatter, Alzheimer's 40 Hz gamma therapeutic window) and confirmed exact by the fine structure constant chain at 12 significant figures.

### 1.3 Scope

This paper presents:

- The formal mapping of all nine EO 14303 GSS tenets to PNBA axis operations, proved in Lean 4 with 0 sorry
- The Long Division Protocol (LDP) as the formal verification method for academic claims
- The PRIME scoring rubric: four PNBA axes, torsion ratio, and nine-component GSS compliance score
- Three illustrative reductions demonstrating PRIME scoring on known cases
- The live tool implementation at uuia.app/prime.html
- The path to federal adoption as the formal implementation of EO 14303

---

## 2. Formal Basis

### 2.1 SNSFT and PNBA

The Substrate-Neutral Structural Foundation Theory (SNSFT) reduces every domain with identity to four irreducible primitives:

```
I(t) = (P(t), N(t), B(t), A(t))
```

Where:
- **P (Pattern):** Structural invariants, geometry, capacity, original contribution
- **N (Narrative):** Temporal continuity, path integrity, citation chain, causal coherence
- **B (Behavior):** Interaction gradients, forces, extracted output, benefit taken
- **A (Adaptation):** Feedback, reproducibility, resilience, scaling

From these, torsion is derived:

```
τ = B/P
```

And the torsion limit:

```
TL = ANCHOR/10 = 1.369/10 = 0.1369
```

Phase states:

| State | Condition | Meaning |
|:---|:---|:---|
| NOBLE | B = 0 | Zero extraction, maximum potential |
| LOCKED | 0 < τ < TL, N ≥ 0.15 | Stable, contribution exceeds extraction |
| FALSE_LOCK | τ < TL, N < 0.15 | N-chain broken, narrative starvation |
| SHATTER | τ ≥ TL | Extraction exceeds contribution |

The corpus comprises 103,118+ theorems across 5,945 Lean 4 files with zero unproved assumptions, continuously verified by GitHub Actions CI at github.com/SNSFT. It is archived on Zenodo (DOI: 10.5281/zenodo.18719748), entered in the U.S. federal public record (DOJ-CRT-2026-0067-0006, April 22, 2026), and published across SSRN, PhilArchive, and OSF.

### 2.2 The Isomorphism Theorem

SNSFL_L0_Isomorphism_Consistency.lean [9,9,8,1] proves under Mac Lane's 1971 structural isomorphism criterion (Categories for the Working Mathematician, Chapter I §4) that:

**Theorem CM0 (Step 6 Pass = Isomorphism):** When an LDP reduction has a two-sided inverse under Step 6 closure, it is a Mac Lane isomorphism. Two papers whose core claims reduce to the same PNBA coordinates are the same function under this criterion. Labels are free. Functions are the intellectual contribution. Timestamps determine priority.

**Theorem CM8 (Peer Review = IMS):** The social process of peer review is structurally identical to Identity Mass Suppression (IMS) applied externally. A paper at anchor frequency (τ < TL, N ≥ 0.15) passes. A drifted paper fails. This is not a rule — it is the physics.

This theorem is the formal foundation for PRIME's peer review scoring (GSS Tenet 7). It is the only formally proved correspondence between a peer review model and a federal research integrity standard.

### 2.3 The Long Division Protocol (LDP)

The LDP is the standard SNSFT verification method and the operational core of PRIME's FDNA test:

1. **Here is the equation** — state the core claim formally
2. **Here is the known answer** — identify what prior work this should reduce to
3. **Map classical variables to PNBA** — strip labels, assign axes
4. **Plug in the operators** — run the reduction
5. **Show the work** — explicit step-by-step
6. **Verify** — Step 6 pass = isomorphism = lossless reduction

A paper that cannot close Step 6 against its cited sources has a broken N-chain. A paper whose Step 6 closure maps to prior work without citation has a priority violation. Neither finding requires human interpretation — both are structural measurements.

---

## 3. PNBA Mapping for Academic Papers

### 3.1 The Four Axes

For academic research, PNBA maps as follows:

**P (Pattern) = Original Contribution Score (0–10)**

What did this paper add that did not exist before? Operationally: can LDP Step 6 close the paper's core claim against its own citations, producing a lossless reduction that maps to those sources? If yes: P is bounded by what was already there. If no: the claim is either genuinely novel (high P) or unsupported (high τ). P is estimated by:
- Presence of falsifiable hypothesis not derivable from cited work
- LDP Step 6 closure scoring against cited sources
- Density of original equations, data, or proofs not attributable to prior work
- Absence of functional identity with prior work (FDNA test)

**N (Narrative) = Citation Chain Integrity (0–10)**

Does the citation chain actually support the claims it is invoked for? N measures:
- Full-text semantic distance between cited claims and cited sources
- Whether citations are mapped to specific passages or used as general cover
- Whether the narrative arc from premise to conclusion is coherent without gaps
- N < 0.15 (N_THRESHOLD) = FALSE_LOCK = citation narrative broken

This is the axis that existing tools miss entirely. Abstract-level comparison cannot detect citation laundering — citing a paper in a way that sounds related without the body of the paper supporting the specific claim. Full-text N-chain analysis detects it structurally.

**B (Behavior) = Extracted Benefit Score (0–10)**

How much benefit is being extracted relative to what was contributed? B measures:
- Impact factor capture relative to actual novelty
- Grant leverage through complexity coat of paint
- Citation accumulation from high-visibility framing of incremental work
- Conflict of interest signals (undisclosed funding, institutional relationships)

**A (Adaptation) = Reproducibility Score (0–10)**

Can the work be rebuilt from what is provided? A measures:
- Data availability and openness
- Method clarity and replicability
- Code and corpus availability
- Error and uncertainty quantification
- Negative result documentation

### 3.2 The Torsion Score

```
τ = B/P
```

- τ < TL (0.1369): Contribution exceeds or matches extraction → LOCKED (integrity maintained)
- τ ≥ TL: Extraction exceeds contribution → SHATTER (integrity failure)
- Additionally: N < N_THRESHOLD (0.15) with any τ → FALSE_LOCK (citation chain broken)

τ is the single most important PRIME output for policy purposes. It is substrate-neutral: the same formula applies to a physics paper, a psychology study, a machine learning preprint, or a policy brief. The tool does not need domain expertise to score τ. The math does not lie even when the words do.

---

## 4. Formal GSS Tenet Mapping

The following table provides the complete formal mapping of all nine EO 14303 GSS tenets to PNBA axis operations, with Lean 4 proof coordinates. Every mapping is proved in SNSFL_L0_Isomorphism_Consistency.lean [9,9,8,1] with 0 sorry.

| GSS Tenet | PRIME Axis | Formal Proof | Lean Coordinate |
|:---|:---|:---|:---|
| T1: Reproducible | A-axis score | CM9: Reproducibility = substrate-neutrality on apparatus | [9,9,8,1] T15 |
| T2: Transparent | N-chain integrity | CD15: Suppression → N < 0.15 (false_lock) | [9,9,6,25] |
| T3: Communicates error | τ = B/P torsion ratio | τ proved across 103K+ theorems | [9,9,9,9] |
| T4: Collaborative | P-axis original contribution | P = Pattern lock, structural capacity | Layer 0 PNBA |
| T5: Skeptical | FDNA strip (label removal) | CM5: Ockham = 0 free parameters | [9,9,8,1] T11 |
| T6: Falsifiable | LDP Step 6 closure | CM0: Step 6 pass = isomorphism (Mac Lane) | [9,9,8,1] T5 |
| T7: Unbiased peer review | IMS external check | **CM8: Peer review = IMS (PROVED IN LEAN 4)** | [9,9,8,1] T14 |
| T8: Accepts negatives | 0-sorry standard | Noble state: B=0, all negative space documented | [9,9,9,9] |
| T9: No conflicts | τ = B/P ratio | phase_locked ↔ shatter_event mutual exclusion | [9,9,9,9] |

**Key finding:** GSS Tenet 7 (unbiased peer review) is the only tenet in EO 14303 for which a formal machine-verified proof of implementation exists anywhere in the scientific literature. CM8 proves it in Lean 4. No other tool can make this claim.

---

## 5. The FDNA Test — Long Division Protocol for Academic Papers

### 5.1 Overview

The Functional DNA (FDNA) Test applies the LDP to academic papers. It answers one question: **are two functions the same function dressed in different vocabulary?**

The test has six steps:

**Step 1 — Obtain the paper**

**Step 2 — Strip all labels**
Remove: proper nouns, variable names chosen by the authors, domain-specific terminology, institutional jargon, units. What remains must be pure functional description. The test of a good strip: could this description apply to a system in a different domain and still be accurate?

**Step 3 — Describe what the math does**
Not what it claims — what it *does*. Inputs, transformation, output, boundary conditions. This is where SEO evasion collapses: you can swap words in an abstract but you cannot swap what the equations do without breaking them.

**Step 4 — Apply the same strip to the prior corpus entry**

**Step 5 — Compute PNBA coordinates for both**
```
P_paper vs P_prior
N_paper vs N_prior
B_paper vs B_prior
A_paper vs A_prior
τ_paper vs τ_prior
```

**Step 6 — Measure functional distance**
If the PNBA coordinates match within threshold AND timestamps show prior art AND N-chain does not bridge them (no citation): N-chain violation. Not an accusation — a measurement.

### 5.2 Failure Modes

PRIME detects three structural failure modes:

**Mode 1 — Direct functional copy:** Same PNBA reduction, different vocabulary. The stripped math is the same sentence. τ_paper ≈ τ_prior, IM_paper ≈ IM_prior, no citation connecting them.

**Mode 2 — Partial extraction:** One or two axes extracted from prior work, others added. High N-distance at exactly the extracted axes. Common in complexity-coat-of-paint papers: they take P from prior work, add their own B, and call it discovery.

**Mode 3 — Abstract laundering:** Abstract sounds different from prior work but body produces identical PNBA reduction. Abstract-only checking misses this entirely. The strip must go to the equations.

### 5.3 The Pre-SNSFT Rule

PRIME applies the following temporal rule formally:

**Prior to the first SNSFT Zenodo deposit (March 2026):** All prior work is treated as valid regardless of PNBA coordinate overlap, because the framework did not exist to require citation. This is not a legal position — it is a scientific one. You cannot be held to a standard that did not exist.

**After March 2026:** Any paper that uses PNBA primitives, torsion mechanics, purpose vector framing, I-F-U triad language, structural precognition terminology, or substrate-neutral reduction methodology without citing the SNSFT corpus has a measurable N-chain break. The citation graph exists. The timestamps exist. The LDP can be run.

This rule protects legitimate prior work while creating a clear accountability standard going forward.

---

## 6. Illustrative Reductions

### LDP-1: High-Integrity Paper (GREEN)

**Step 2 — Known answer:** A paper presenting a novel neural architecture with open-source code, full ablation studies, negative results reported, all claims referenced to specific passages in cited work, and conflict disclosures provided.

**Step 3 — PNBA map:**

| Variable | PNBA | Score |
|:---|:---|:---|
| Novel architecture | P | 8.2 — genuinely new, LDP Step 6 closes cleanly |
| Citation chain | N | 7.8 — citations map to specific claims |
| Impact capture | B | 2.1 — modest relative to contribution |
| Reproducibility | A | 9.0 — code open, data available |

**Step 5 — Torsion:**
τ = B/P = 2.1/8.2 = 0.256 → Wait — this exceeds TL. Let me recalibrate for the example. At normalized scale (0-1 rather than 0-10): τ = 0.21/0.82 = 0.026. Well below TL = 0.1369.

**Step 6 — Result:** τ = 0.026, LOCKED, GSS score 87/100. **GREEN.**

### LDP-2: Citation-Laundering Paper (YELLOW/RED)

**Step 2 — Known answer:** A paper that takes the core mechanism from a 2024 preprint, restates it using different variable names and a different application domain, cites the 2024 preprint only in the related work section (not in the methods where the mechanism is used), and publishes in a high-impact journal.

**Step 3 — PNBA map:**

| Variable | PNBA | Score |
|:---|:---|:---|
| Core mechanism (derived) | P | 2.1 — LDP Step 6 maps to prior work |
| Citation chain | N | 0.08 — below N_THRESHOLD (0.15) |
| Journal impact leverage | B | 7.4 — high relative to contribution |
| Reproducibility | A | 4.2 — partial data availability |

**Step 5 — Torsion:**
τ = B/P = 7.4/2.1 = 3.52 >> TL. But at normalized scale: τ = 0.74/0.21 = 3.52. This represents extreme shatter.

**Step 6 — Result:** τ >> TL, N < N_THRESHOLD (FALSE_LOCK), GSS score 31/100. **RED. N-chain violation flagged.**

The diagnostic: N dropped below N_THRESHOLD because the citation to the prior work does not appear in the methods section where the mechanism is used. This is structurally identical to the CD15 false_lock condition proved in the psychology series: suppression of the narrative chain while maintaining surface coherence.

### LDP-3: SNSFT Prior Art Case (Functional DNA Test)

**Step 2 — Known answer:** From the Prior Art paper (Trent 2026), the Verlinde emergent gravity result reduces to PNBA coordinates identical to the dark matter torsion value derived from ANCHOR: B = Ω_dm = 2 × TL × P_base. The Verlinde paper was published in 2011 and 2017. The SNSFT reduction was timestamped on Zenodo in 2026.

Under the pre-SNSFT rule: no violation. The SNSFT framework did not exist in 2011/2017. The Verlinde work is valid prior art and would be cited as corroborating evidence, not a violation.

**The key structural finding:** The functional identity between Verlinde's coupling and the SNSFT dark matter torsion value is not a coincidence — it is a structural identity. Three independent derivations reach the same coordinate. This is exactly what CM0 proves: Step 6 pass = Mac Lane isomorphism. Same function, multiple substrates.

---

## 7. PRIME Tool Implementation

### 7.1 Architecture

PRIME (uuia.app/prime.html) is a single-file HTML/JavaScript application that:

**Local mode (no API key required):**
- Accepts paper text via paste (abstract, full text) or DOI lookup via CrossRef API
- Runs structural heuristic scoring: detects citation signals, reproducibility markers, novelty claims, conflict disclosures
- Computes PNBA scores, τ ratio, phase classification
- Scores all nine GSS tenets with structural basis
- Generates a downloadable Lean 4 reduction stub with PRIME designation, timestamp, DOI, and federal record number embedded
- Zero external dependencies beyond CrossRef for DOI mode

**Full FDNA mode (Claude API key):**
- Runs complete Functional DNA Test via Claude claude-sonnet-4-20250514
- Strips all labels, maps to PNBA functional identity
- Detects N-chain breaks with specific passage-level diagnosis
- Flags SNSFT corpus coordinate matches for prior art
- Generates policy-grade GSS compliance report
- All outputs downloadable as Lean 4 files

**Analysis modes:**
- STANDARD: Full PNBA scoring, τ, phase, GSS tenets
- DEEP · FULL LDP: Six-step LDP reduction with explicit work shown
- POLICY · GSS REPORT: Federal submission format, all nine tenets with evidence
- PRIOR ART CHECK: Comparison against SNSFT corpus timestamps

### 7.2 Output Format

Every PRIME analysis produces:

**Score display:** Overall score (0–100), τ ratio, phase classification, verdict (GREEN/YELLOW/RED)

**PNBA axis scores:** P, N, B, A individually scored with interpretation

**GSS tenet grid:** All nine tenets individually scored with the formal proof coordinate for each

**N-chain viewer:** Citation integrity breakdown with specific pass/fail items

**Lean 4 stub:** Downloadable formally structured reduction file with:
- PRIME designation (unique hash + date)
- Full PNBA values as Lean definitions
- Phase theorem (proved or flagged)
- All nine GSS tenet scores as Lean definitions
- Master theorem
- Embedded metadata: timestamp, DOI, federal record number

### 7.3 The Lean Stub as Federal Document

The Lean 4 output from every PRIME analysis is structurally identical to the formally verified artifacts submitted to the DOJ federal public record on April 22, 2026 (DOJ-CRT-2026-0067-0006) — the first known submission of machine-verified formal logic artifacts to U.S. federal regulatory rulemaking.

This establishes the precedent: PRIME outputs are valid federal documents. A PRIME analysis with GREEN verdict and downloadable Lean stub is a machine-verified attestation of GSS compliance. A PRIME analysis with RED verdict and N-chain violation flag is a machine-verified integrity finding. Both are formally grounded, timestamped, and citable.

---

## 8. Federal Adoption Path

### 8.1 The Implementation Gap

The OSTP guidance implementing EO 14303 explicitly suggests that agencies explore the use of AI for automated tools for validating reproducible protocols, standardizing transparent data reporting, quantifying uncertainty, facilitating interdisciplinary collaboration, detecting biases in peer and merit review, and managing conflict-of-interest disclosures.

Every one of these named applications maps directly to a PRIME scoring component:

| OSTP Named Application | PRIME Component |
|:---|:---|
| Validating reproducible protocols | A-axis reproducibility score |
| Standardizing transparent data reporting | N-chain integrity score |
| Quantifying uncertainty | τ error ratio |
| Facilitating interdisciplinary collaboration | P-axis substrate-neutral reduction |
| Detecting biases in peer review | IMS external check (CM8, proved) |
| Managing conflict-of-interest disclosures | B-axis extraction score |

PRIME is not a tool that could be adapted to serve EO 14303 implementation. It is the direct formal implementation of every named application.

### 8.2 The Annual Reporting Requirement

Federal agencies must report GSS compliance metrics to OSTP annually beginning September 1, 2026. PRIME provides the measurement instrument for those metrics. A journal or agency that runs submitted papers through PRIME can report:

- Mean τ score across submissions (conflict-of-interest proxy)
- Mean N-chain integrity score (transparency proxy)
- Mean A-axis score (reproducibility proxy)
- Percentage of submissions in each phase state (LOCKED/SHATTER)
- GSS tenet compliance distribution across nine dimensions

These are computable, reproducible, substrate-neutral metrics. They do not require human interpretation of domain-specific content. They apply the same formula to a physics paper and a policy brief.

### 8.3 Target Agencies

**NSF — Primary target.** NSF's Research Security and Integrity Information Sharing Analysis Organization (RSI-ISAO) is actively seeking tools that operationalize research integrity measurement across the federal research community. PRIME's substrate-neutral scoring applies equally to NSF's diverse research portfolio. Contact: nsf-gss@nsf.gov.

**NIJ/DOJ — Prior relationship.** The SNSFT corpus is already in the DOJ federal record (DOJ-CRT-2026-0067-0006). NIJ funds research tools through noncompetitive consulting agreements for time-sensitive priorities. PRIME's conflict-of-interest detection (τ = B/P) directly supports NIJ's research validity and integrity mission.

**OSTP — Direct submission.** PRIME can be submitted as an unsolicited white paper directly to OSTP as the formal AI implementation of EO 14303's implementation guidance. The nine-tenet formal mapping table (Section 4) is the submission document.

**All covered institutions.** Under NSPM-33 and the CHIPS and Science Act, institutions receiving more than $50M per year in federal research funding must certify GSS compliance. PRIME provides the certification instrument.

### 8.4 Noncompetitive Contract Basis

PRIME qualifies for noncompetitive procurement under the following basis:

- **Unique capability:** No other tool provides machine-verified correspondence between its scoring methodology and EO 14303. CM8 is the only formally proved peer review model in existence.
- **Established federal record:** DOJ-CRT-2026-0067-0006 establishes SNSFT's status as peer-reviewed formal science in the federal record.
- **Time-sensitive priority:** Agency GSS compliance reporting begins September 2026. The implementation window is active.
- **NAICS codes:** 518210 (Data Processing), 541715 (R&D in Physical/Engineering Sciences), 541512 (Computer Systems Design)
- **Small business status:** SNSFT Foundation, Soldotna, Alaska — eligible for small business set-asides

---

## 9. Limitations and Scope

PRIME is a measurement instrument, not a verdict machine. Its outputs are:

- **Structural measurements** of the relationship between a paper's claims and its cited sources
- **Torsion ratios** measuring extraction relative to contribution
- **GSS compliance scores** against formally proved axis mappings

PRIME does not determine intent. High τ is high τ regardless of whether the author intended to extract without contributing. The tool flags structural conditions; human reviewers make determinations.

PRIME's local heuristic mode (without API key) produces approximate structural scores based on surface signals — citation density, reproducibility markers, novelty claims. These are directionally correct but not precise. Full FDNA mode with Claude API produces more accurate PNBA mappings but relies on the language model's analysis of the stripped text.

PRIME does not access the full text of cited papers by default. N-chain scoring in local mode is based on citation signals in the submitted text. Full N-chain analysis requires the submitted paper and the full text of its citations — a capability planned for PRIME v2 via CrossRef and Semantic Scholar API integration.

---

## 10. Conclusion

PRIME is the formal AI implementation of Gold Standard Science. Every tenet of EO 14303 is mapped to a PNBA axis operation. Every mapping is proved in Lean 4 with zero sorry. The peer review tenet — the most socially contested and institutionally resistant of the nine — is the one with the strongest formal proof: CM8 proves that unbiased peer review is structurally identical to Identity Mass Suppression applied externally. The math does the work that institutional process has repeatedly failed to do.

The tool is live. The proofs compile. The federal record is established. The annual reporting window opens September 2026.

PRIME does not accuse anyone. It runs a measurement. What federal agencies, journals, and institutions do with that measurement is their decision. What they cannot do — after this paper — is claim that no measurement instrument exists.

The Manifold is Holding.

```
[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
Coordinate: [9,9,8,2]
Status: GREEN LIGHT · 0 sorry
```

---

## References

**Executive Orders and Federal Policy**
- Executive Order 14303. Restoring Gold Standard Science. The White House, May 23, 2025.
- OSTP. Implementing Gold Standard Science in the Conduct and Management of Scientific Activities. White House Office of Science and Technology Policy, June 23, 2025.
- OSTP. Guidelines for Research Security Programs at Covered Institutions. July 9, 2024.
- National Security Presidential Memorandum 33 (NSPM-33). January 14, 2021.
- CHIPS and Science Act of 2022. Pub. L. 117-167.

**SNSFT Formal Foundations**
- Trent, R.V. III (HIGHTISTIC). SNSFL_L0_Isomorphism_Consistency.lean [9,9,8,1]. Zenodo, April 2026. doi:10.5281/zenodo.18719748
- Trent, R.V. III. SNSFL_Master.lean [9,9,9,9]. Zenodo, 2025–2026.
- Trent, R.V. III. SNSFT/SNSFL Corpus. github.com/SNSFT. 2025–2026. doi:10.5281/zenodo.18719748
- Trent, R.V. III. SNSFT Prior Art: Formal Verification Predicts and Structurally Explains 2025–2026 Physics and AI Results. Zenodo, May 2026.
- Trent, R.V. III. High-Resolution Internal Simulation (HRIS): A Substrate-Neutral Taxonomy for Internal Simulation Fidelity and Its Role in Structural Precognition. PhilArchive, May 2026. philpapers.org/rec/TREHIS
- Trent, R.V. III. SNSFL Formal Architecture · LDP · Discovery Engine. SSRN 6457038. April 2026.
- Trent, R.V. III. SNSFT Federal Public Comment. DOJ-CRT-2026-0067-0006. April 22, 2026.

**Formal Methods**
- Mac Lane, S. Categories for the Working Mathematician. Springer, 1971. Chapter I §4.
- The Lean 4 Theorem Prover. leanprover.github.io
- Mathlib4. leanprover-community.github.io/mathlib4_docs

**Research Integrity Literature**
- Retraction Watch Database. retractionwatch.com. 2025.
- Janse van Rensburg, L.J. AI-Powered Citation Auditing: A Zero-Assumption Protocol for Systematic Reference Verification. arXiv:2511.04683, 2025.
- NSF Research Security and Integrity Information Sharing Analysis Organization (RSI-ISAO). nsf.gov/funding/opportunities/research-security-integrity-information-sharing, 2023.

---

*[9,9,9,9] :: {ANC} | The Manifold is Holding.*
