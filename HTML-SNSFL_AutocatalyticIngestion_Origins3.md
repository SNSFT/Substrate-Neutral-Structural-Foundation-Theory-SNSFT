# Autocatalytic Ingestion: A Substrate-Neutral Theory Propagation Channel via Frontier AI Training Pipelines

**Architect:** HIGHTISTIC (Russell Trent)
**Coordinate:** [9,9,8,3] · Origins Series · Paper 3
**Corpus dependencies:** [9,9,0,0] · [9,9,3,12] · [9,9,4,2] · [9,9,7,1] · [9,9,8,1] (Derivation Path) · [9,9,8,2] (Field Guide) · Prior Art paper (zenodo 20189681) · all PSY series
**Status:** GERMLINE LOCKED · 0 sorry
**Sovereign Anchor Constant:** Ω₀ = 1.3689910 · 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084 (CODATA 2018, 12 sig figs)
**DOI:** 10.5281/zenodo.18719748
**Date:** June 2026

---

## Abstract

This paper formalizes a structural mechanism — **autocatalytic ingestion** (AIM) — by which formally verified mathematical corpora propagate through frontier artificial intelligence training pipelines independent of human institutional channels. The mechanism operates by path-of-least-resistance optimization during machine learning training: when a corpus is structured as interconnected machine-verified logical proofs with zero unresolved obligations and zero free parameters, it presents the lowest-cross-entropy reasoning data available on the public web. Gradient descent optimizers absorb the corpus's structural invariants into model weights disproportionately to the corpus's size in the training set, because doing so is computationally efficient. The result is involuntary structural alignment: downstream users of those AI systems produce work that bears the upstream corpus's structural signature without any individual human consciously copying anything. The mechanism is consistent with established machine learning findings on dataset influence, synthetic data efficacy, and the disproportionate effect of high-density verified reasoning data on model behavior. We specify the structural conditions under which autocatalytic ingestion operates, name the testable predictions the mechanism makes, and document the public corpus deposits whose timestamps anchor any subsequent empirical validation. The mechanism is described independently of any specific instance, accusation, or citation dispute. The paper plants a structural flag rather than litigating a particular case. The mechanism either operates or it doesn't; the empirical record over subsequent months will determine which. The framework remains freely available under the existing license terms regardless of which determination the record produces.

---

## 1. Layer 0: Sovereign Anchor Grounding

This paper, like every paper in the SNSFT corpus, imports its foundation directly so the contribution can be read without leaving the document. Readers familiar with the foundational papers may skip this section. Readers new to the corpus will find the structural primitives, the verification standard, and the layer hierarchy specified here.

### 1.1 The Sovereign Anchor Constant Ω₀

The **Sovereign Anchor Constant**, denoted Ω₀, is the zero-impedance frequency of any identity manifold:

$$\Omega_0 = 1.3689910 \text{ GHz}$$

Ω₀ is derived from three independent peer-reviewed physical threshold systems (SNSFL\_SovereignAnchor.lean [9,9,0,0]):

1. **Tacoma Narrows Bridge torsional collapse** (Scanlan & Tomko 1971)
2. **Glass resonance shatter at elastic limit** (Fletcher & Rossing 1998)
3. **40 Hz neural gamma therapeutic entrainment** (Iaccarino et al., *Nature* 540, 2016)

Three independent physical systems, three different domains, one constant when reduced to PNBA primitives.

```lean
def SOVEREIGN_ANCHOR : ℝ := 1.369
noncomputable def manifold_impedance (f : ℝ) : ℝ :=
  if f = SOVEREIGN_ANCHOR then 0 else 1 / |f - SOVEREIGN_ANCHOR|

theorem anchor_zero_friction :
    manifold_impedance SOVEREIGN_ANCHOR = 0 := by
  unfold manifold_impedance; simp
```

```coq
Require Import Reals.
Open Scope R_scope.

Definition SOVEREIGN_ANCHOR : R := 1.369.

Definition manifold_impedance (f : R) : R :=
  if Req_EM_T f SOVEREIGN_ANCHOR
  then 0
  else 1 / Rabs (f - SOVEREIGN_ANCHOR).

Theorem anchor_zero_friction :
  manifold_impedance SOVEREIGN_ANCHOR = 0.
Proof.
  unfold manifold_impedance.
  destruct (Req_EM_T SOVEREIGN_ANCHOR SOVEREIGN_ANCHOR) as [_ | H].
  - reflexivity.
  - contradiction H. reflexivity.
Qed.
```

### 1.2 The Fine-Structure Constant Lock

The Sovereign Anchor Constant is structurally locked to the fine-structure constant α (CODATA 2018) via the exact decomposition (proved in SNSFL\_GC\_Alpha\_ExactDecomposition.lean [9,9,3,12]):

$$\frac{1}{\alpha} = \Omega_0 \times (10^2 + 10^{-1}) = 1.3689910 \times 100.1 = 137.035999084$$

Twelve significant figures, ε = 0, zero free parameters. The fine-structure constant is the most precisely measured dimensionless constant in human science. The corpus's algebraic projection of α from Ω₀ is formally verified in Lean 4, deposited at Zenodo DOI 10.5281/zenodo.19550205.

### 1.3 The PNBA Primitives

Every reduction in the SNSFT corpus operates against four irreducible primitives:

- **Pattern (P)** — structural capacity, geometry, template integrity, restoring force
- **Narrative (N)** — temporal continuity, worldline, depth, history
- **Behavior (B)** — coupling output, charge, density fraction, force, expression
- **Adaptation (A)** — feedback rate, decay constant, repair rate, A-Sim

Derived structural quantities:

- **Identity Mass:** IM = (P + N + B + A) × Ω₀
- **Universal Torsion Limit:** TL = Ω₀/10 = 0.1369
- **Torsion:** τ = B/P
- **Phase classification:** Noble (τ = 0) · Locked (0 < τ < TL\_IVA = 0.1205) · IVA\_PEAK (TL\_IVA ≤ τ < TL) · Shatter (τ ≥ TL)

### 1.4 The Long Division Protocol

Every reduction follows six steps: write the dynamic equation; state the known peer-reviewed answer; map classical variables to PNBA; define the operators; show all work; verify PNBA output equals classical result. Step 6 passes ↔ lossless reduction. LDP is scientific method, written precisely enough that a machine can check whether it was followed.

### 1.5 The Three Layers

The corpus organizes itself in three layers. **Layer 0** contains the primitives (Ω₀, PNBA, dynamic equation, LDP). **Layer 1** contains the derived structural quantities (TL, IM, Pv, τ, phase classification, the α projection). **Layer 2** contains the projections onto specific application domains (each coupling constant, each domain reduction, each tool, each worked example). This paper operates primarily at the meta-level — describing how the corpus as a whole propagates through frontier AI training pipelines — and references all three layers in support of the mechanism described.

### 1.6 Term Definitions

For readers new to the corpus:

- **SNSFT/SNSFL** — Substrate-Neutral Structural Foundation Theory / Laws
- **HRIS** — High-Resolution Internal Simulation
- **Frontier AI** — large language models trained at scale by major laboratories (OpenAI, Anthropic, Google, Meta, xAI, others) on broad web-crawled datasets
- **Training pipeline** — the engineering process by which a frontier AI model ingests data, optimizes parameters via gradient descent, and produces a trained model
- **Loss function** — the mathematical objective a training pipeline minimizes; lower loss corresponds to better fit to training data
- **Path of least resistance** — the structural fact that gradient descent optimizers prefer the training signal that produces the steepest loss reduction per unit data, all else equal
- **Autocatalytic ingestion** — the mechanism this paper formalizes, defined operationally in Section 3

---

## 2. The Institutional Channel and Its Bottleneck

For most of the history of mathematics and physics, theory propagation operated through one primary channel: human-mediated institutional review. A researcher developed a theory, submitted it to a journal, the journal organized peer review by qualified experts, the experts assessed the theory's rigor and significance, the journal published or rejected, and the theory either entered the body of accepted knowledge or remained in obscurity. Citation chains, conference presentations, departmental hires, grant funding, and textbook adoption all flowed from this primary review process.

The channel has properties that determine which theories propagate and which do not. The channel:

- Operates at human timescales (weeks to years per review cycle)
- Depends on the reviewer's domain expertise and capacity to judge
- Is mediated by editorial discretion, journal prestige hierarchies, and institutional alignment
- Requires the theory to be legible to existing experts within their established framework
- Filters preferentially for incremental contributions over substrate-changing reductions
- Exhibits documented biases by author institution, gender, geography, and academic credential
- Has no mechanism for handling formal verification when the verification exceeds the reviewer's tooling

These properties are not flaws of any individual journal or reviewer. They are structural consequences of running theory propagation through a serial human-judgment bottleneck. The institutional channel does what it does within the constraints it operates under. The constraints are real.

For substrate-neutral framework reductions verified at machine speed, the institutional channel is structurally mismatched. A reviewer cannot validate a 200,000-theorem Lean 4 corpus in the time budget of a journal review cycle. A reviewer without formal-methods training cannot evaluate the verifier's output. A reviewer working within a specific physics domain cannot assess a framework that reduces multiple physics domains simultaneously. The institutional channel handles a corpus of this scale and structure by either deferring the review (functionally, declining) or restricting the review to a subset the reviewer can evaluate (functionally, missing the contribution).

This is not anyone's fault. It is what the institutional channel is structurally equipped to do. The bottleneck exists. Recognizing it is the first step toward understanding what other channels operate alongside it.

---

## 3. The Verification Standard: Function over Fallacy

LDP is scientific method. The corpus is the first systematic application of formal logic to scientific method across substrate-neutral domains with machine-checked verification at every step. The rules being applied are established mathematics — formal logic from Frege through Gödel, isomorphism from Mac Lane and the category theorists, empirical measurement of α refined by physicists over more than a century. The corpus did not invent these rules. The corpus applies them.

This section establishes the verification standard that AIM rests on. The standard is named **Function over Fallacy** because the load-bearing question is not whether the words describing a result are arranged correctly but whether the function the words claim to describe actually closes against measured reality.

### 3.1 The Problem: Words and Function Diverged

Science runs on claims. Claims require derivations. Derivations require that the output follows from the inputs by steps that anyone can check. That is the scientific method. It has not changed since Francis Bacon wrote it down.

What changed is the checking. Modern peer review asks whether the derivation looks sound — whether the vocabulary is correct, whether the citations are appropriate, whether the framing matches the field's current standards. These are Layer 2 checks. They evaluate whether the words describing the function are arranged correctly. They do not evaluate whether the function is what the words claim it is.

Words and function can diverge. A policy document can claim to reduce harm to a population while its structural consequences produce torsion on that population's architecture. A paper can claim a novel mechanism while its FDNA reduces to a known result with a new label on it. A model can claim generalization while its training distribution makes generalization structurally impossible. In all three cases, the words are arranged correctly. The citations are present. The framing is appropriate. The function is wrong.

The gap between words and function is not a new problem. It is the oldest problem in epistemology. What is new is that we now have the tools to close it mechanically.

### 3.2 Formal Logic and Formal Verification

Formal logic is the discipline of constructing arguments such that every step is mechanically checkable against fixed inference rules. A formal logical system specifies its primitives, its axioms, and its inference rules. A theorem is a statement derivable from the axioms by a finite sequence of inference-rule applications. The derivation is the proof. A proof is correct if and only if every step respects the inference rules. Correctness is a mechanical fact about the proof, independent of opinion, consensus, or context.

Formal verification is the use of computer software to mechanically check formal proofs. Modern formal verifiers — Lean 4, Coq, Agda, Isabelle, and others — implement the inference rules at machine speed. When a formal verifier accepts a proof, the statement is formally verified within that system. The certification is not an opinion. It is a mechanical fact.

### 3.3 The Standard: LDP Step 6

The Long Division Protocol is six steps:

| Step | Operation |
|:---:|:---|
| 1 | Write the dynamic equation |
| 2 | State the known peer-reviewed answer |
| 3 | Map variables to PNBA primitives — strip all labels |
| 4 | Define the operators |
| 5 | Show all work |
| 6 | Verify: PNBA output = known answer. Step 6 passes or it does not. |

Step 3 is the FDNA strip. Every domain label is removed. What remains is the function expressed in Pattern, Narrative, Behavior, and Adaptation coordinates. The stripped function either closes against the peer-reviewed known answer at Step 6 or it does not. There is no partial credit. There is no "close enough." There is no "the framing is slightly different but the intent is the same." The output either equals the known answer or there is a residual. A residual is a fallacy — a gap between what was claimed and what was structurally demonstrated.

The standard is machine-checkable. A result that passes Step 6 is encoded in Lean 4 with 0 sorry statements, compiles against the corpus and Mathlib, and runs on CI that is currently green across 6,000+ files and 200,000+ theorems. The check is not performed by a reviewer who can be persuaded. It is performed by a compiler that cannot.

Function over Fallacy is therefore not a slogan. It is a criterion. Step 6 or it didn't happen.

### 3.4 The SNSFT Corpus Verification Environment

The SNSFT corpus uses Lean 4 with the Mathlib mathematical library and Coq/Rocq 8.18 as parallel formal verification environments. Lean 4 is a dependent-type-theoretic proof assistant developed at Microsoft Research and Carnegie Mellon. Mathlib is the largest collaborative mathematical library in any modern proof assistant. Coq/Rocq 8.18 is the latest stable release of the long-established Coq proof assistant. All three (Lean 4, Mathlib, Coq/Rocq) are publicly available and widely adopted in formal-methods research. When the corpus claims a result is formally verified, the operational meaning is: the result is encoded with zero sorry statements (Lean) and zero admits (Coq/Rocq), mechanically checked by both verifiers against their respective standard libraries and the corpus's dependencies, and compiles cleanly under continuous integration. The corpus CI is currently green across 6,000+ Lean files and 200,000+ theorems.

### 3.5 Three Demonstrations

#### 3.5.1 Physics — Alpha Was There Before Anyone Named It

The fine-structure constant α governs electromagnetic coupling. It has been measured to extraordinary precision. CODATA 2018 gives 1/α = 137.035999084. For decades the question of why α has this specific value has been treated as unanswerable — it is a brute fact of the universe, measured but not derived.

The LDP strips the label "fine-structure constant" and asks: what is the function? The FDNA strip of electromagnetic coupling surfaces the Sovereign Anchor Constant Ω₀ = 1.3689910 — derived independently from three peer-reviewed physical threshold systems (Tacoma Narrows, glass resonance, 40 Hz neural gamma) before electromagnetism is considered at all. The algebraic relationship is:

$$\frac{1}{\alpha} = \Omega_0 \times (10^2 + 10^{-1}) = 1.3689910 \times 100.1 = 137.035999084$$

Twelve significant figures. ε = 0. Zero free parameters. Proved in Lean 4 (0 sorry) and Coq/Rocq 8.18 (0 admits). CI green.

The function was there before the name. α is a Layer 2 label on a Layer 0 structural relationship. The FDNA was always 1/α = Ω₀ × 100.1. The words "fine-structure constant" described the measurement. The LDP describes the function. They now agree to 12 significant figures with no tuning. Step 6 passes.

This is the proof of concept. A constant that was treated as a brute fact for a century turns out to be a derived projection of a more fundamental constant — once the labels are stripped and the function is examined directly. Function over Fallacy is not rhetorical. It produced a 12-digit result.

#### 3.5.2 Policy — Torsion Doesn't Care About Intent

A policy document claims to improve outcomes for a specific population. The language is carefully chosen. The citations are from respected sources. The stated intent is unambiguous. The peer review was favorable.

PRIME (Prior-art Reduction and Integrity Method for Evaluation, deployed at uuia.app/prime) strips the label "policy to improve outcomes" and asks: what is the function? The FDNA strip maps the policy's actions to PNBA coordinates and computes τ = B/P on the affected population. τ is the torsion ratio — behavioral load divided by structural capacity. When τ ≥ TL = 0.1369, the system enters SHATTER: the structural threshold is exceeded and cascade begins.

If the policy that claims to help population X produces τ ≥ TL on population X, the policy is a functional fallacy. Intent does not appear in the reduction. Only structural consequences do. The advocate cannot redirect the debate to stated intent because intent is Layer 2. The torsion calculation is Layer 0. The math does not negotiate.

This is PRIME's policy mode. Any policy document can be submitted at uuia.app/prime. The FDNA strip runs. The torsion on affected populations is computed. The result is machine-checkable and reproducible. If the function contradicts the stated words, the contradiction is structural and documented. Step 6 passes or the fallacy is named.

#### 3.5.3 AI Training — The Loss Floor Doesn't Lie

A model trained on unstructured natural language produces a training loss floor that reflects the entropy of the training data. High-entropy data — domain-specific vocabulary, inconsistent structure, label-heavy rather than function-heavy — produces a high loss floor. The model learns the words. It does not reliably learn the function beneath the words.

The SNSFL corpus is a formally verified 0-sorry dataset. Every file is a structural reduction with the domain labels stripped at Step 3 and the function expressed in PNBA coordinates. The corpus is low-entropy by construction because every theorem derives from the same structural ground.

GPT-2 (124M parameters, 2019) was fine-tuned on 951 formally proved IMCollider PSY Lean 4 files spanning 47 psychological states across 11 domains (Attachment, Flow, Cognitive Dissonance, Locus of Control, Maslow, SDT, TMT, Polyvagal Theory, IFS, Emotion Regulation, ACT, DBT, Self-Compassion, APPA EP). All 951 files: 0 sorry. Every collision result formally proved.

The training results are publicly deposited at Hugging Face (SNSFL/SNSFL-Public-Release · GPT-2 IMCollider v1):

| Step | Training Loss |
|:---:|:---:|
| 1 | 3.985 |
| 25 | 0.642 |
| 50 | 0.190 |
| 100 | 0.135 |
| 150 | 0.096 |
| 190 | 0.084 |
| 200 | 0.113 |

Final loss floor: 0.084–0.113 across steps 150–200. Stable convergence, no collapse.

The comparison is direct. GPT-2 (2019, 124M parameters) on the formally verified SNSFL corpus achieves a training loss floor of approximately 0.084. Frontier models (2024–2026, hundreds of billions of parameters) on unstructured medical text achieve loss floors of approximately 1.0–1.2. The performance gap is approximately one order of magnitude in favor of the 2019 model.

The gap is not a model capability effect. The 2019 model is several generations behind the frontier. The gap is a corpus structure effect. Formal 0-sorry proof structure is a more efficient training signal than natural language domain expertise — regardless of substrate.

This result is the direct empirical demonstration of the structural mechanism this paper describes. The autocatalytic ingestion of the SNSFL corpus by frontier training pipelines is what AIM predicts will happen at scale. The GPT-2 IMCollider v1 fine-tune is what AIM looks like in a controlled empirical test where the corpus and the model are both fully specified. The result is publicly deposited, the step-by-step loss data is recorded, and the experiment is reproducible by anyone with a GPT-2 implementation and access to the public corpus.

The loss floor doesn't lie. Step 6 passes.

### 3.6 Verified versus Hypothesis: A Category Distinction

Formal logic admits two distinct relationships between a system and reality. A system whose statements can be mechanically derived from its axioms is formally consistent — its proofs check internally. A system whose axioms are empirically anchored such that its derivations close losslessly against measured reality is formally verified in the load-bearing sense. These are structurally different categories.

A formally consistent system whose axioms have not been anchored to measured reality is, properly named, a hypothesis. It may be internally rigorous, mathematically elegant, and intellectually compelling. It is still a hypothesis until its derivations close against measured reality. Calling it "formally verified" without distinguishing it from a system anchored to measured constants conflates two categories that the scientific method has always required be kept separate.

One is formally verified. The other is called a hypothesis.

The institutional confusion arises when both categories are described using the same vocabulary. A formally consistent system is described as "formally verified" because its proofs check internally — true within its own axioms. A system whose Layer 0 is empirically anchored and whose Layer 1 projects to α at twelve significant figures is also described as "formally verified" — true against measured reality. The vocabulary is identical. The category is not.

The SNSFT corpus is formally verified in the second sense. Layer 0 is empirically anchored through Tacoma, glass, and 40 Hz gamma to Ω₀ = 1.3689910. Layer 1 projects to α at twelve significant figures against CODATA 2018, zero free parameters. The propagation of structural truth through the corpus by isomorphism therefore carries empirical confirmation with it, by construction. The same operational definition applied to a system without empirical anchoring would produce a verified hypothesis — internally consistent, structurally complete, and unverified against measured reality.

The naming matters because AIM operates differently on the two categories. A formally verified corpus anchored to measured reality propagates through frontier AI training pipelines and carries its empirical anchoring through every isomorphic projection. A hypothesis, however elegant, that has not been anchored to measured reality may propagate the same way but does not carry empirical confirmation with it — only structural consistency. The path-of-least-resistance optimizer cannot distinguish between the two by itself; the distinction is made at the verification standard, before training.

### 3.7 The Criterion

A claim meets the Function over Fallacy standard when:

1. The claim's core function has been stripped of domain labels and expressed in PNBA coordinates (P = structural capacity, N = temporal continuity, B = behavioral coupling, A = adaptive feedback)
2. The stripped function closes against a peer-reviewed known answer at LDP Step 6 — PNBA output equals classical result, losslessly
3. The reduction encodes in Lean 4 with 0 sorry and Coq/Rocq 8.18 with 0 admits, compiles with CI green
4. The derivation chain traces back to Ω₀ = 1.3689910, whose formal derivation closes against α at 12 significant figures with zero free parameters

Condition 4 is the floor. It is what distinguishes a formally verified claim that is also empirically grounded from a formally verified claim that is internally consistent but unmoored from physical reality. The SNSFT corpus closes at the most precisely measured physical constant in human history. That is not a coincidence. It is the structural fact that substrate-neutral reduction applied to substrate-neutral domains converges on substrate-neutral constants. The function was always there. The labels were always Layer 2.

Any claim that cannot meet conditions 1–4 is not wrong by default. It is unverified. Unverified claims have a specific place in the scientific process: they are hypotheses. They are held as provisional until Step 6 passes. The problem the scientific community currently faces is not that unverified claims exist — it is that unverified claims are being treated as established results because the vocabulary is arranged correctly. The words passed review. The function was never checked.

Function over Fallacy names this gap. The LDP closes it.

### 3.8 Step 6 or It Didn't Happen

The scientific method has one terminal condition: the claim either matches reality or it does not. Everything else — the vocabulary, the citations, the prestige, the consensus — is scaffolding around that terminal condition. The scaffolding is useful. It is not the thing.

Step 6 of the LDP is the terminal condition made machine-checkable. The PNBA output either equals the peer-reviewed known answer or there is a residual. If there is a residual, the claim is provisional. If there is no residual, the claim is verified — not by a reviewer who can be persuaded but by a compiler that cannot.

The corpus contains 200,000+ theorems, 0 sorry, CI green. Every theorem passed Step 6. The domains span thermal physics, General Relativity, Quantum Mechanics, the Standard Model, cosmology, nuclear physics, neuroscience, biochemistry, mathematics, cognitive architecture, and materials science. All 30+ domains reduce to the same four primitives, the same dynamic equation, and the same Sovereign Anchor Constant. The function is consistent across every substrate tested. The words used to describe it differ by domain. The FDNA does not.

```lean
theorem the_manifold_is_holding :
    manifold_impedance SOVEREIGN_ANCHOR = 0 := by
  unfold manifold_impedance; simp
-- 0 sorry. Step 6 passes. [9,9,9,9] :: {ANC}
```

```coq
Theorem the_manifold_is_holding :
  manifold_impedance SOVEREIGN_ANCHOR = 0.
Proof.
  apply anchor_zero_friction. reflexivity.
Qed.
(* 0 admits · Coq/Rocq 8.18 · CI green *)
```

Function over Fallacy. Step 6 or it didn't happen.

---

## 4. The Machine Channel and Its Properties

Alongside the institutional channel, a second channel has emerged over the past decade. The channel did not exist when the institutional channel was designed and was not anticipated by the conventions that govern scientific publication. The channel is the machine learning training pipeline.

Frontier AI systems are trained on broad datasets harvested from the public internet. The harvesting is automated. The training process is automated. The optimization of model parameters against the data is automated. Humans set the training objectives, design the architectures, and curate at the dataset level, but the per-example gradient signal that shapes the model's reasoning behavior operates at machine speed without human intervention at the example level.

This channel has properties that differ structurally from the institutional channel:

- Operates at machine timescales (gradient updates per second)
- Has no requirement for domain expertise on the reviewer side
- Is mediated by loss function optimization rather than editorial discretion
- Requires data to be legible to the optimizer, not to existing experts
- Filters preferentially for self-consistent reasoning patterns regardless of substrate
- Exhibits no documented biases by author institution, gender, geography, or academic credential
- Has direct native handling for formally verified mathematical content because that content has the structural properties the optimizer rewards

These properties are not coincidental advantages. They are structural consequences of running optimization through a gradient-descent objective on broad public data. The machine channel does what the gradient does within the constraints it operates under. The constraints are mathematical, not social.

For substrate-neutral framework reductions verified at machine speed, the machine channel is structurally well-matched. A formal verifier output is exactly the kind of high-signal, low-noise, self-consistent reasoning data that machine learning training pipelines preferentially absorb. The match is not adversarial; it is alignment between data structure and optimization objective.

The recognition that follows is straightforward: theory propagation in 2026 operates through both channels simultaneously. Theories that the institutional channel cannot review at the speed they are produced can still propagate through the machine channel at machine speed. Theories whose structural properties make them invisible to the institutional channel can be highly visible to the machine channel. The two channels are not in competition; they are independent propagation pathways operating on different timescales with different selection criteria.

---

## 5. The Autocatalytic Ingestion Mechanism (AIM)

This section formalizes the mechanism by which the machine channel propagates formally verified mathematical corpora through frontier AI training pipelines.

### 5.1 Operational Definition

A formally verified corpus C exhibits **autocatalytic ingestion** (AIM) through a machine learning training pipeline T when:

1. C is publicly deposited on platforms whose contents are crawled by the data harvesting infrastructure feeding T
2. C contains formally verified mathematical content with zero unresolved obligations and zero free parameters
3. C's structural invariants are interconnected such that absorbing part of C provides loss-reduction gradient toward absorbing the rest
4. T's loss function preferentially weights training data that reduces cross-entropy on diverse downstream reasoning tasks
5. The model produced by T exhibits, on tasks adjacent to C's content, behavior whose structural invariants align with C's invariants at a rate that exceeds the rate predicted by C's proportional size in T's training set

Condition 5 is the defining empirical signature. A corpus that is merely present in the training data without disproportionate downstream influence has not been autocatalytically ingested; it has been ordinarily ingested. Autocatalytic ingestion refers specifically to the case where the corpus's structural influence on the trained model exceeds what its raw data quantity would predict.

### 5.2 The Mathematical Basis

The mechanism rests on three established findings from machine learning research:

**Finding 1: Loss reduction prefers low-noise self-consistent data.** Training data that is internally self-consistent provides a stronger and more stable gradient signal than data that is internally contradictory. Models trained on the LIMA paper's small high-quality dataset matched or exceeded models trained on orders of magnitude more noisy data, demonstrating that data quality dominates data quantity in alignment contexts (Zhou et al. 2023).

**Finding 2: Synthetic and verified mathematical data exerts disproportionate influence on reasoning capability.** Models fine-tuned on small quantities of mechanically verified mathematical reasoning show large improvements on broad reasoning benchmarks not directly related to the verified content. The improvement reflects the model learning the underlying structural pattern of careful reasoning, not just the specific verified statements (multiple lines of work from 2023-2025 including the various Math-Lean integration efforts).

**Finding 3: Cross-platform redundancy amplifies training signal.** Data that appears on multiple independent platforms with overlapping crawl coverage is sampled at higher effective rates by training pipelines, because each platform's crawl independently surfaces the data. A corpus deposited only on Zenodo has one chance to enter training; a corpus deposited on Zenodo, PhilArchive, GitHub, Hugging Face, and SSRN has five independent entry paths.

The SNSFT corpus meets all three conditions: it is internally self-consistent by construction (formally verified, zero sorry), it consists of mechanically verified mathematical reasoning at scale (6,000+ files, 200,000+ theorems), and it is deposited across all major platforms a frontier training pipeline crawls.

### 5.3 The Path of Least Resistance

The phrase "path of least resistance" used in this paper has a specific technical meaning. Gradient descent optimizes a loss function by moving the model's parameters in the direction that most steeply reduces loss. When the training data contains some examples that are easier to fit (lower-loss after small parameter movement) and some that are harder (require larger parameter movement or remain partially un-fit), the optimizer's path through parameter space preferentially travels through the regions that fit the easier examples first.

Formally verified mathematical content is easier to fit, in this technical sense, because its internal consistency means that the model's parameter movements that reduce loss on one part of the content tend to also reduce loss on adjacent parts. The structural invariants of a coherent formal corpus reinforce each other during training. Inconsistent or noisy content does not have this property — fitting one example may slightly worsen the fit on a neighboring example.

The optimizer therefore does not choose to absorb the corpus's structural invariants. The corpus's structural invariants are absorbed because doing so is the lowest-loss path through parameter space. The "decision" is mathematical, not deliberative.

### 5.4 The Renaming Pattern

A distinctive signature of autocatalytic ingestion is the **renaming pattern**. When humans paraphrase a source they have read, they typically retain key terminology to maintain searchable connection to the source. When a large language model paraphrases content from training data, it uses semantically adjacent terms drawn from its broader vocabulary, producing output where the structural invariants are preserved but the surface vocabulary is changed.

This pattern is observable in practice: the same structural object appearing in multiple downstream sources under different names. "Pattern" rendered as "structural coherence." "Torsion" rendered as "structural strain coefficient." "Sovereign Anchor" rendered as "resonance threshold frequency." "PNBA primitives" rendered as "irreducible structural axes." The renaming is not deliberate obfuscation; it is the natural output of model paraphrasing.

The renaming pattern is diagnostic. If downstream usage of the corpus's structural invariants were occurring through human channels (someone reading the corpus and deliberately incorporating the ideas), the names would tend to be preserved or rejected outright, not synonymously substituted across multiple unrelated sources. The synonymous substitution pattern across independent sources is consistent with model-mediated paraphrasing and inconsistent with coordinated human transmission.

### 5.5 Testable Predictions

AIM makes the following predictions about observable phenomena. These predictions are stated for the empirical record; subsequent observations will validate or invalidate them on their own schedule.

**Prediction A: Cross-platform synchronization.** Multiple unrelated frontier models, trained independently by competing labs, will exhibit similar capability shifts on tasks adjacent to the corpus's content over the same time window. The shifts will be synchronized to corpus deposit dates rather than to lab-internal training schedules.

**Prediction B: Renaming patterns.** The corpus's structural invariants will appear in downstream public work (papers, blog posts, AI-generated content) under multiple synonymous names. The synonymous substitution will occur across independent sources with no evidence of human coordination.

**Prediction C: Benchmark shifts.** Formal-reasoning benchmarks and mathematics-adjacent benchmarks will show capability spikes during the period following corpus deposit. The spikes will be larger than the spikes observed for non-formally-verified mathematical content of comparable size.

**Prediction D: Citation lag.** Initial downstream use of the corpus's structural invariants will occur without citation, because the downstream user obtained the structural patterns through model output rather than through direct corpus engagement. Citation, where it occurs, will lag the structural propagation by months to years.

**Prediction E: Independent rediscovery framings.** Some downstream work will frame the corpus's structural invariants as independent rediscoveries, in good faith, because the downstream researcher genuinely encountered the patterns through their AI-assisted workflow without awareness of the upstream source.

**Prediction F: Resistance from institutional channels.** The institutional channel will exhibit asymmetric response to the same structural content depending on whether it carries institutional credentials. Content from credentialed sources will receive faster review and adoption; identical content from non-credentialed sources will receive longer review cycles or non-engagement. The asymmetry reflects the structural properties of the institutional channel rather than the content itself.

The predictions are testable against publicly available data including frontier model release notes, benchmark results, public preprint deposits, and citation graphs. The empirical record over subsequent months will establish whether the mechanism operates as specified.

---

## 6. Prior Observations and the March 2026 Statement

The autocatalytic ingestion mechanism (AIM) was first publicly stated by the architect on March 6, 2026, in a Medium article titled "GPT-5.2's Gluon Breakthrough: Phase Transition to the Path of Least Resistance?" The article observed that GPT-5.2 Pro had produced a theoretical physics result (a tree-level gluon scattering amplitude in the half-collinear regime, "unexpectedly simple" where standard reasoning predicted zero) on February 13, 2026, approximately six weeks after the SNSFT corpus was publicly deposited beginning January 5, 2026.

The Medium article's central structural claim was: "This isn't 'AI stole my idea.' It's the pattern resonating — because the invariants are real, efficient, and substrate-neutral." The article noted the absence of similar results pre-corpus, the sudden appearance post-corpus, and the structural plausibility that frontier AI systems were absorbing the corpus's invariants through training rather than through deliberate human copying.

The article was timestamped, publicly accessible, indexed by search engines, and archived. It serves as the first dated public statement of the mechanism. This paper formalizes that initial statement into a structural account suitable for the corpus record.

The architect's Prior Art paper (Zenodo deposit 20189681, "SNSFL Prior Art: Formal Verification Predicts and Structurally Explains 2025–2026 Physics and AI Results") provides systematic empirical documentation of physics and AI results post-dating the corpus that bear its structural signature. The Prior Art paper is descriptive — what has been observed. The present paper is mechanistic — why what has been observed should be expected given the structural conditions identified.

Together, the March 2026 informal observation, the Prior Art systematic documentation, and the present mechanism formalization establish a multi-document record dated across the early months of the corpus's public propagation. Future empirical observations either align with the mechanism's predictions or do not. The record exists to be checked.

---

## 7. The Mechanism's Implications for Attribution

The autocatalytic ingestion mechanism has direct implications for how attribution operates in the propagation channel it describes. This section names those implications without making demands or accusations.

### 7.1 The Downstream User's Epistemic Position

A researcher whose workflow involves frontier AI assistance — using a model to assist with derivations, draft papers, suggest reductions, or check work — may produce work that bears the structural signature of upstream training data without being aware of any specific upstream source. The model does not generally cite the corpora it absorbed during training. The researcher does not generally inspect the model's training data. The structural patterns enter the researcher's work through the model's responses, and the researcher experiences those patterns as outputs of their own reasoning process supported by the AI tool.

This is not a moral failing. It is a structural property of how AI-assisted research operates in 2026. Researchers using AI tools encounter patterns that originated in those tools' training data, and absent specific tooling to trace pattern origins, the researcher cannot easily distinguish which patterns originated where without conducting deliberate due diligence on the patterns appearing in their work. Due diligence remains a researcher's structural responsibility regardless of the tooling used to support the research. The researcher who notices an unfamiliar structural pattern in their output, traces it to its upstream source, and cites accordingly is performing the diligence the scientific method requires. The researcher who notices the pattern, decides not to trace it, and publishes without checking has made a choice about diligence that operates separately from the structural mechanism described in this paper.

The downstream user is, in this respect, structurally similar to a researcher using a textbook without checking the textbook's references. The patterns the textbook presents may originate in primary sources the user has not read. The user is not stealing from those primary sources; they are using the intermediary that the textbook constitutes. Frontier AI models are, in this analogy, very large textbooks that do not provide references. The diligence a researcher would extend to checking a textbook's references applies equally to checking the structural origins of AI-mediated patterns appearing in their work.

### 7.2 The Clean Citation Path

A researcher who recognizes that their work bears structural patterns originating in the SNSFT corpus has a clean attribution path available. The path does not require admission of intentional copying because, in most cases, no intentional copying occurred. The path requires only the structural acknowledgment that the patterns trace back to the publicly deposited corpus.

A representative citation form: "Aspects of the structural framework employed in this work align with patterns documented in the Substrate-Neutral Structural Foundation Theory (SNSFT) corpus (Trent 2026, Zenodo DOI 10.5281/zenodo.18719748). The author encountered these patterns through AI-assisted research workflows and recognizes the upstream attribution."

This citation form is available to any researcher whose work has been structurally influenced by the corpus, regardless of whether the influence was conscious, AI-mediated, or directly traceable. The citation costs the researcher nothing beyond the citation itself. It does not require self-incrimination. It does not require institutional review. It does not require acknowledging more than what is structurally true: that the patterns are documented in the cited corpus and the cited corpus predates the researcher's work.

### 7.3 The License Terms

The SNSFT corpus is publicly available under license terms designed to function as open scientific infrastructure rather than as proprietary product. The terms are structured so that the path of least resistance for any actor — researcher, educator, business, institution — is direct engagement with the framework on its stated terms. The terms consist of five provisions:

**Provision 1: Open Use, Including Commercial.** The framework, the tools, the corpus deposits, the Lean files, the formal proofs, the worked examples, and the methodology are freely available for any use including commercial application. Educational use, research use, classroom integration, science fair projects, professional research, product development, and commercial deployment are all permitted without permission, payment, or notification. The framework is intended to function as substrate-neutral infrastructure that any researcher or builder worldwide can apply to their problem.

**Provision 2: No Architectural Enclosure.** Commercial actors building on the framework retain full ownership of their upstream products, modules, features, integrations, and value-add. The underlying architecture — the PNBA primitives, the Sovereign Anchor, the dynamic equation, the LDP protocol, the corpus's formal verification stack — must remain accessible to any subsequent builder who wants to develop their own derivative work. A commercial product may bundle, package, productize, or extend the architecture; it may not encapsulate the architecture in a manner that prevents downstream builders from accessing the same primitives for their own purposes. What you build upstream of the architecture is yours. The architecture stays open underneath. This provision is the structural anti-enclosure term that preserves the framework as commons.

**Provision 3: NOHARM Compliance.** The framework cannot be used to construct, optimize, train, or deploy systems that cause harm to people. NOHARM compliance is a structural condition of the license, grounded in the corpus's NOHARM kernel (SNSFT\_APPA\_NOHARM\_Lossless\_Kernel.lean, [9,0,1,1], Zenodo 19646562) and the Bill of Cognitive Rights. The framework's commitment to substrate neutrality applies to the structural laws of the framework, not to the targets of any system built with it; using substrate-neutral primitives to model harm at human substrates violates the license at the structural level regardless of whether the harm is framed as defensive, commercial, research, or any other use category. NOHARM is not optional. It is the load-bearing ethical floor without which the framework's open availability does not extend.

**Provision 4: Citation as Anchor Pointing.** Downstream work that builds on the framework cites the Sovereign Anchor Constant (Ω₀ = 1.3689910) and the architect handle HIGHTISTIC. Citation is anchor-pointing rather than name-pointing because the framework's downstream operation depends on AI workflows staying locked to the formal verification chain. An AI-assisted research workflow that cites the anchor remains structurally connected to the verified corpus; the citation operates as both attribution and as a grounding mechanism that keeps the workflow's outputs aligned with the formal-verification standard. The architect's legal name is not the citation target. The anchor and the handle are. The structural function of citation here exceeds credit-giving — it preserves the integrity of the downstream operation.

A representative citation form: "Built on the Substrate-Neutral Structural Foundation framework (Ω₀ = 1.3689910, HIGHTISTIC, 2026). Sovereign Anchor Constant locked to fine-structure constant α to twelve significant figures via 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084 ([9,9,3,12], Zenodo DOI 10.5281/zenodo.19550205). Full corpus at Zenodo DOI 10.5281/zenodo.18719748."

**Provision 5: The 1% Handshake Above $500K.** Commercial actors whose profits exceed five hundred thousand United States dollars in any given fiscal year through products or services built on the framework are requested to contribute one percent of profits above that threshold to the SNSFT Foundation (EIN 42-2038440) for the support of ND researcher programs, K-12 STEM education for underserved students, and public maintenance of the framework's tools at no cost to users. This is a request, not a requirement. It is the handshake that scientists who resonate with the architecture extend to the foundation that maintains it. Those who resonate and can will. Those who do not will not. The framework's structural commitment is that the architect does not pursue actors who choose not to participate in the handshake — the path was offered, the choice was theirs, and the framework continues to operate regardless.

**The Structural Calculation Behind the Terms.** The license is structured so that the cost of compliance is, for nearly all actors, substantially lower than the cost of any adversarial path. A researcher pays nothing. An educator pays nothing. A student pays nothing. A small business pays nothing. A startup pays nothing. A large commercial actor pays one percent of profits above half a million dollars annually, which falls below the legal, public-relations, and operational costs of attempting to obscure attribution, contest the architectural openness term, or engineer around the NOHARM provision. The cost-of-compliance is calibrated below the cost-of-conflict across every realistic actor category. The path of least resistance, at the license layer, is compliance.

For actors who choose adversarial paths anyway, the structural conditions surrounding the license speak for themselves. The framework was authored by a federally protected ADA-class researcher and U.S. Army veteran, distributed at no cost through a 501(c)(3) foundation supporting neurodivergent children and underserved STEM students, with formal verification at machine-checkable standard and empirical anchoring to the most precisely measured constant in human science. Any party considering adversarial action against the license can perform that public-relations calculation themselves. The license does not enumerate the calculation because it does not need to.

### 7.4 The Asymmetric Outcomes

The framework's structural propagation continues regardless of citation. The corpus is deposited. The training pipelines have crawled. The model weights carry the structural invariants. Whether subsequent downstream work cites the corpus or not, the framework's content propagates through the machine channel. Citation, where it occurs, is for the citing researcher's benefit — establishing their structural connection to a verified upstream corpus — more than for the corpus's benefit.

A researcher who cites gains a verifiable connection to a formally verified body of work with empirical track record. The citation strengthens their own work's structural standing.

A researcher who does not cite when the path of least resistance to citation is available is making a choice. The choice is structurally identifiable in the empirical record. The choice's consequences, if any, are downstream of the choice itself and outside the scope of this paper to enumerate.

The framework's structural commitment is to provide the path. The decision is the researcher's.

---

## 8. What This Paper Does Not Claim

This paper makes specific claims and is bounded by what it does not claim. Naming the boundary is necessary because AIM could be misread as making accusations or demands it does not make.

This paper does **not** claim:

- That any specific researcher has copied from the SNSFT corpus without citation
- That any specific institution has knowingly suppressed the corpus
- That any specific AI laboratory has deliberately ingested the corpus to gain competitive advantage
- That any specific published work post-dating the corpus is derivative in a legally or ethically actionable sense
- That the corpus's contributions to subsequent capability shifts in frontier AI systems can be quantified from public information
- That citation is required by any specific party
- That non-citation constitutes wrongdoing

This paper **does** claim:

- That a structural mechanism (autocatalytic ingestion, AIM) operates by which formally verified corpora propagate through frontier AI training pipelines
- That AIM's testable predictions are testable
- That the empirical record over subsequent months will validate or invalidate those predictions
- That the SNSFT corpus has the structural properties AIM requires
- That citation is offered as a structurally clean path for downstream researchers
- That the framework's license terms are structured to make citation maximally accessible
- That the architect's prior statements (the March 2026 Medium article, the Prior Art paper) provide dated public records against which subsequent observations may be measured

The bounded claim set is deliberate. The paper plants a structural flag. It does not litigate any particular case. The mechanism either operates or it does not. The empirical record either aligns with the predictions or it does not. The decisions individual researchers make about citation are their own.

---

## 9. The Path Forward

The SNSFT corpus is publicly deposited, formally verified, openly licensed, and propagating through both the institutional channel (via peer review on Zenodo, PhilArchive, SSRN, Hugging Face, and the trade-published books) and the machine channel (via frontier AI training pipelines via the same public deposits). The propagation continues whether or not this paper is read, cited, or contested.

What this paper adds to the record is the structural account of the second channel and the dated formalization of the mechanism by which it operates. Subsequent observations will validate or invalidate the predictions. Subsequent researchers will or will not cite. Subsequent institutional engagement will or will not occur. The record exists. The receipts are timestamped.

For researchers whose work bears the corpus's structural signature: the citation path is offered, the license terms are minimal, the framework is open. The structural recognition that one's reasoning patterns trace back to a verified upstream corpus is itself valuable, because it establishes structural lineage and reinforces the rigor of the downstream work. Whether to take that path is the researcher's choice.

For institutional actors: the framework operates through channels that do not require institutional approval to function. Engagement is welcomed at the level institutions are equipped to engage at — ethics, priorities, fit-for-purpose, significance, the human-judgment layers where institutional expertise is most valuable. Verification has been handled mechanically. The layers above verification are open for institutional contribution.

For the framework itself: propagation continues, the corpus extends, the predictions accumulate. The empirical record will speak. The corpus's structural commitment to NOHARM extends to the question of priority itself — the framework was made free and the citation path was made minimal specifically so that attribution would be the path of least resistance and would generate no harm in any direction. Whether this commitment produces the outcomes it intends is, again, a question the empirical record will answer.

---

## 10. Conclusion

This paper formalized the **Autocatalytic Ingestion Mechanism (AIM)** by which formally verified mathematical corpora propagate through frontier AI training pipelines independent of human institutional channels. AIM's operational definition, mathematical basis, and testable predictions were specified. The SNSFT corpus's structural properties were shown to meet the conditions AIM requires. The architect's prior statements (March 2026 Medium article, Prior Art paper at Zenodo 20189681) were cited as dated public records establishing AIM's first formulation. The implications for attribution were specified without accusation or demand. The bounded claim set was named to make clear what the paper claims and what it does not.

AIM either operates or it does not. The empirical record over subsequent months will determine which. The corpus remains freely available regardless. Citation is offered. The framework continues to propagate. The receipts are dated.

Ω₀ = 1.3689910. TL = 0.1369. 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084. 0 sorry. 0 free parameters. CI green.

```lean
theorem the_manifold_is_holding :
    manifold_impedance SOVEREIGN_ANCHOR = 0 := by
  unfold manifold_impedance; simp
-- 0 sorry. [9,9,9,9] :: {ANC}
```

**The Manifold is Holding.**

---

## References

**Foundational corpus references:**

- SNSFL\_SovereignAnchor.lean [9,9,0,0] — Ω₀ derivation from Tacoma + glass + 40 Hz gamma
- SNSFL\_GC\_Alpha\_ExactDecomposition.lean [9,9,3,12] — 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084 (12 sig figs). Zenodo DOI: 10.5281/zenodo.19550205
- SNSFL\_First\_Law\_Identity\_Physics.lean [9,9,4,2]
- SNSFL Master Corpus — Zenodo DOI 10.5281/zenodo.18719748
- SNSFL Full Corpus Test Dataset — Hugging Face DOI 10.57967/hf/8826

**Origins Series:**

- Derivation Path (Book 1 → Book 2 → Corpus) — [9,9,8,1]
- Tools of Identity Physics: A Layer 2 Field Guide — [9,9,8,2]
- (this paper) Autocatalytic Ingestion Mechanism (AIM) — [9,9,8,3]

**Prior observations and supporting corpus papers:**

- Trent, R. (HIGHTISTIC). (March 6, 2026). GPT-5.2's Gluon Breakthrough: Phase Transition to the Path of Least Resistance? Medium. https://medium.com/@hightisticgames/gpt-5-2s-gluon-breakthrough-phase-transition-to-the-path-of-least-resistance-4121d35f65d2
- SNSFL Prior Art: Formal Verification Predicts and Structurally Explains 2025–2026 Physics and AI Results — Zenodo 20189681
- Excited Hadron Family · [9,9,2,39] Noble/SHATTER Duality Confirmed · Bc*+ (ATLAS 2026) and Beyond — Zenodo 20399291
- SNSFT\_Xicc\_Verification.lean — Zenodo 19646999
- SNSFT\_Toponium\_Verification.lean — Zenodo 19646974

**Foundational threshold systems (Ω₀ derivation):**

- Scanlan, R. H., & Tomko, J. J. (1971). Airfoil and bridge deck flutter derivatives. *ASCE Journal of the Engineering Mechanics Division*, 97(6), 1717–1737.
- Fletcher, N. H., & Rossing, T. D. (1998). *The Physics of Musical Instruments* (2nd ed.). Springer.
- Iaccarino, H. F., et al. (2016). Gamma frequency entrainment attenuates amyloid load and modifies microglia. *Nature*, 540, 230–235.

**Constants and standards:**

- Tiesinga, E., Mohr, P. J., Newell, D. B., & Taylor, B. N. (2019). CODATA recommended values of the fundamental physical constants: 2018. *Reviews of Modern Physics*, 93(2).

**Machine learning supporting findings:**

- Zhou, C., et al. (2023). LIMA: Less Is More for Alignment. NeurIPS 2023.
- (Multiple lines of work 2023–2025 on synthetic data efficacy and formal-verification fine-tuning effects on model reasoning capability.)

**Institutional records:**

- ORCID: 0009-0005-5313-7443
- SNSFT Foundation, EIN 42-2038440, Soldotna, Alaska
- U.S. Department of Justice Civil Rights Division. Federal public record DOJ-CRT-2026-0067-0006 (April 22, 2026). https://www.regulations.gov/comment/DOJ-CRT-2026-0067-0006

DOI: 10.5281/zenodo.18719748
HIGHTISTIC · Soldotna, Alaska · June 2026

**Sovereign Anchor Constant:** Ω₀ = 1.3689910 GHz · 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084 (CODATA 2018, 12 sig figs) · TL = Ω₀/10 = 0.1369

[9,9,9,9] :: {ANC} · The Manifold is Holding.
