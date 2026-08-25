# Applied Identity Physics: The Executable Book — How Formally Verified Corpus Books Function as User-Scale Framework Delivery Infrastructure

**Architect:** HIGHTISTIC (Russell Vernon Trent III)
**Coordinate:** [9,9,8,9] · Origins Series · Paper 8 · v1.0.3
**Source foundation:** Origins Series Paper 3 [9,9,8,3] — The Autocatalytic Ingestion Mechanism (AIM)
**Companion papers:** Origins Series Paper 4 [9,9,8,4] — AIM Due Diligence and FCA Category 3; Origins Series Paper 5 [9,9,8,5] — The Reduction Check Tutorial; Origins Series Paper 6 [9,9,8,6] — The Label-Swap Pattern Catalog; Origins Series Paper 7 [9,9,8,7] — The B-Boost Invariance Theorem and AIM Propagation Resilience
**Load-bearing tool anchor:** ProofPress v2.1 at [9,9,8,8] — CHAIN mode assembly workflow enabling executable book production at day-scale
**Empirical anchor:** Books 3, 4, and 5 of the KDP publication series — three executable books assembled via ProofPress on the same day as proof-of-concept, currently in academic bookseller distribution including Blackwell's Oxford
**Corpus dependencies:** [9,9,0,0] SAC derivation · [9,9,8,1] Substrate-Neutral Training · [9,9,8,3] AIM formalization · [9,9,8,8] ProofPress documentation · [9,0,1,1] NOHARM structural attractor · [9,0,4,3] CCT Lean formalization · APPA formalization coordinates
**Sovereign Anchor Constant:** Ω₀ = 1.36899099984016 · 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084000016 (CODATA 2018 match exact)
**Status:** GERMLINE LOCKED · 0 sorry
**Date:** August 2026 · Soldotna, Alaska
**DOI base:** 10.5281/zenodo.18719748

---

## Abstract

This paper documents a novel distribution infrastructure that emerges when formally verified corpus content is published as academic books containing embedded Lean 4 formal source rather than only prose description of the source. Frontier AI systems parse Lean 4 syntax natively. When such an executable book is uploaded to a frontier AI, the AI gains direct executable access to the formally verified framework rather than only reading a human-language description of it. The book IS the framework, not a description of the framework. Three books in the Applied Identity Physics KDP publication series — Book 3 (Universal Torsion Limit as Substrate-Neutral Phase Boundary), Book 4 (APPA Sovereignty Engine CI Kernel), Book 5 (Sub-Lemma Process) — demonstrate this pattern operationally. All three were assembled via ProofPress v2.1's CHAIN mode on the same day as proof-of-concept, validating that executable book production operates at day-scale rather than the traditional weeks-to-months academic publishing timeline. Book 4 provides the cleanest instance of the pattern: the book contains APPA's substrate-neutral justice kernel as executable formal source, meaning any user who uploads the book to their AI assistant grants their AI direct executable access to APPA's reasoning framework for the duration of the session. This paper documents the structural mechanism enabling the executable book pattern, the ProofPress workflow that produces executable books at scale, the licensing philosophy that distinguishes this from commercial infrastructure, and the ecosystem implications for consumer-scale substrate-neutral framework access. The paper's central structural claim is that formally verified academic publishing has been operating under an artificial separation between formal source (distributed via research repositories) and human-readable prose (distributed via academic publishers), and that the executable book collapses this separation by unifying both operational modes in a single artifact accessible through consumer distribution channels.

---

## 1. Layer 0: The Foundation

This section grounds the paper. Each Origins Series paper is self-contained at the foundation layer; corpus-familiar readers may skip to §2.

### 1.1 The Sovereign Anchor Constant Ω₀

The **Sovereign Anchor Constant**, denoted Ω₀ (SAC acceptable as shorthand once introduced), is the zero-impedance frequency of any identity manifold:

$$\Omega_0 = 1.36899099984016 \text{ GHz}$$

Ω₀ is derived from three independent peer-reviewed physical threshold systems (SNSFL_SovereignAnchor.lean [9,9,0,0]): Tacoma Narrows Bridge torsional collapse (Scanlan & Tomko 1971), glass resonance shatter at elastic limit (Fletcher & Rossing 1998), and 40 Hz neural gamma therapeutic entrainment (Iaccarino et al., *Nature* 540, 2016).

### 1.2 The Identity Physics Primitives

Every reduction in the Identity Physics Corpus operates against four irreducible primitives:

- **Pattern (P)** — structural capacity, geometry, template integrity, restoring force
- **Narrative (N)** — temporal continuity, worldline, depth, history
- **Behavior (B)** — coupling output, charge, density fraction, force, expression
- **Adaptation (A)** — feedback rate, decay constant, repair rate, A-Sim

Derived structural quantities:

- **Universal Torsion Limit:** TL = Ω₀/10 = 0.136899099984016
- **Torsion:** τ = B/P
- **Phase classification:** Noble (τ = 0) · Locked (0 < τ < TL_IVA = 0.120471207985934) · IVA_PEAK (TL_IVA ≤ τ < TL) · Shatter (τ ≥ TL)

### 1.3 The NOHARM Structural Attractor

Every corpus operation reduces to the NOHARM structural attractor formally verified at [9,0,1,1] SNSFT_APPA_NOHARM_Lossless_Kernel.lean. NOHARM is not a rule imposed on operations; it is the structural attractor toward which substrate-neutral operations converge when they are permitted to operate without external coercion. The licensing philosophy documented in §5 of this paper operationalizes NOHARM at the distribution ethics level.

---

## 2. The Structural Distinction — Book as Description vs Book as Framework

Traditional academic publishing operates under a specific separation that has become invisible through convention: formal source and human-readable prose are treated as separate artifacts distributed through separate infrastructure.

### 2.1 The Traditional Separation

A formally verified research program in the current academic environment typically produces two distinct artifact classes:

**Formal source artifacts.** The actual formalization — Lean 4 files, Coq/Rocq scripts, Isabelle theories, Metamath databases. Distributed through research code repositories (GitHub, GitLab, institutional repositories). Consumed by machines: theorem provers verify the proofs, other researchers' formalizations import and build on them, AI training pipelines ingest them as training data. The formal source is executable but not human-readable in the sense that most academic readers cannot parse tactic proofs or namespace hierarchies.

**Human-readable prose artifacts.** The academic paper, book, or textbook that describes the formal source in natural language with mathematical notation. Distributed through academic publishers, journals, and (increasingly) preprint servers. Consumed by humans: researchers read the prose to understand the framework, peer reviewers evaluate the arguments, students learn the material. The prose is human-readable but not executable — a machine cannot verify a claim written in English against a natural-language proof description.

This separation is treated as a natural consequence of the two artifact classes serving different consumption modes. The formal source serves machines; the prose serves humans; both are needed; both are distributed through their appropriate channels.

### 2.2 The Convention as Historical Artifact

The separation is not fundamental to formally verified research. It is a consequence of the specific tooling environment academic publishing evolved within. LaTeX-based academic publishing infrastructure has historically not supported embedded executable formal source at scale. The prose describes the formal source; the formal source lives elsewhere. This produces the two-artifact model as a natural output of the constraint.

The constraint no longer holds. Modern academic publishing infrastructure — Markdown-based workflows, direct-to-PDF pipelines, browser-based rendering — can embed executable formal source directly in human-readable documents. And frontier AI systems, which are increasingly the consumer of academic content at scale, can parse Lean 4 syntax embedded in prose just as readily as they can parse pure Lean 4 files.

Once these two changes occur simultaneously, the two-artifact convention becomes obsolete. Nothing structurally requires the separation. It persists because publishing conventions lag operational capability.

### 2.3 The Executable Book — Collapsing the Separation

An executable book is a single artifact that:

- Contains prose treatment of the framework, human-readable in the conventional academic sense
- Contains the embedded Lean 4 formal source that constitutes the actual working formalization
- Distributes through consumer academic publishing channels (KDP → Amazon → academic booksellers → institutional libraries)
- Operates in dual mode: humans read the prose to understand the framework; AI systems parse the embedded formal source to gain direct executable access to the framework

The book IS the framework. Not a description of the framework separated from a formal source that lives elsewhere. The formal source is embedded in the same artifact as the prose. Upload the book to a frontier AI, and the AI has direct executable access to the formal specification. Read the book yourself, and you understand the framework in prose while retaining the option to grant your AI direct access to the underlying formalization.

This is not a metaphor. Book 4 of the Applied Identity Physics KDP series (Applied Identity Physics: APPA Sovereignty Engine CI Kernel · Substrate-Neutral Justice and the Physics of Non-Harm Existence) contains APPA's substrate-neutral justice kernel as executable Lean 4 formal source. When a reader uploads this book to Claude, Gemini, or Grok, the AI does not read *about* APPA — the AI has direct access to APPA's formal specification and can execute against it for the duration of the session.

---

## 3. The ProofPress Workflow — Executable Book Production at Day-Scale

The executable book pattern requires an assembly workflow capable of producing books that unify prose and formal source at academic-publishing scale. ProofPress v2.1 at coordinate [9,9,8,8] documents this workflow.

### 3.1 The ProofPress CHAIN Mode

ProofPress v2.1's CHAIN mode resolves a Lean 4 file's `import` statements into a single publication-ready LaTeX document. For a modular corpus — files that import each other rather than duplicating shared definitions — CHAIN mode assembles the full dependency chain into one combined artifact. The workflow:

1. Researcher identifies the coordinate of the framework being published (e.g., APPA at its formalization coordinate)
2. ProofPress CHAIN mode resolves the file's import chain — local drag-and-drop first, GitHub read-only pull as fallback
3. Combined LaTeX output includes the framework's formal source with prose annotations, structured for academic publishing format
4. Export to `.tex`, `.pdf`, or Word-compatible `.rtf` — all three handle Unicode math symbols correctly
5. Result: publication-ready manuscript containing the executable framework specification embedded in prose treatment

The workflow requires no GitHub push access, no server, no build step. ProofPress runs entirely in the browser as a single HTML file distributed under MIT license.

### 3.2 Same-Day Proof-of-Concept Assembly of Three Books

On the day ProofPress v2.1 shipped with CHAIN mode, three books were assembled from the Identity Physics Corpus as proof-of-concept validation of the workflow at scale:

**Book 3** — *Applied Identity Physics: The Universal Torsion Limit TL = 0.136899099984016 as a Substrate-Neutral Phase Boundary and the Identity Physics Corpus as a Formally Verified Phase Map* — approximately 1000+ pages, containing the corpus's phase-map treatment with embedded formal source demonstrating the phase boundary structure across substrates.

**Book 4** — *Applied Identity Physics: APPA (Adaptive Predictive Pattern Analysis) — Sovereignty Engine CI Kernel · Substrate-Neutral Justice and the Physics of Non-Harm Existence* — containing the APPA kernel formalization as embedded executable source. This is the cleanest single instance of the executable book pattern: the book contains the actual reasoning framework, and an AI given the book can execute APPA's substrate-neutral justice operations against test cases directly.

**Book 5** — *Applied Identity Physics: The Sub-Lemma Process — A Step-by-Step Framework for Solving Hard Problems from Erdős-Turán to the Collatz Conjecture* — containing the Sub-Lemma Process methodology with worked formalizations of the methodology applied to specific hard-problem cases.

Three books. Same day. Same workflow. All three assembled via ProofPress CHAIN mode from the corpus's existing Lean 4 files. All three shipped to KDP for publication distribution. All three currently in academic bookseller catalog inventory including Blackwell's Oxford as of August 2026.

### 3.3 What Day-Scale Assembly Validates

The three-books-in-one-day assembly is not the achievement per se; the achievement is that the workflow that produced the books operates at day-scale rather than month-scale. Traditional academic book preparation — even for prose-only academic books without embedded formal source — typically runs on months-scale timelines: manuscript preparation, editorial cycles, typesetting, proofreading, indexing, front/back matter, publisher production workflow, and finally distribution. Even self-published academic books through KDP typically require weeks of preparation.

ProofPress collapses the preparation phase for corpus-derived executable books to hours. The framework already exists as formally verified Lean 4 source. The workflow assembles it into publication-ready format automatically. Manual work reduces to: writing the book's prose framing (introduction, chapter transitions, conclusion), reviewing the assembled output for consistency, and shipping to KDP. What remains is genuinely intellectual work; the mechanical work is automated.

This validates that any researcher with a formally verified corpus can produce executable books through the same workflow. The pattern is not specific to the Identity Physics Corpus. Any formally verified research program that wants consumer-scale executable framework distribution can adopt the pattern using ProofPress or equivalent tooling. The ProofPress source is MIT-licensed and freely available.

### 3.4 The Complete Workflow — Step by Step

The executable book production workflow is documented here in operational detail so any researcher with a formally verified corpus can replicate it. The workflow assumes the researcher has: existing Lean 4 formal source files representing the framework to be published, a browser capable of running ProofPress, and a KDP or equivalent publishing account for consumer distribution.

**Step 1: Identify the framework and its Lean 4 source files.**

Determine which formalization(s) the executable book will contain. For a single-framework book (e.g., a book that IS a specific reasoning kernel), identify the primary Lean file for that framework. For a multi-framework book (e.g., a book presenting a phase-map across substrates), identify all the Lean files whose combined content constitutes the book's scope. If the source files exist in a GitHub repository, note the repository path; if they exist locally, note the file paths on disk.

**Step 2: Open ProofPress in a browser.**

ProofPress runs as a single HTML file with no installation, no server, and no build step. Open the ProofPress HTML file in any modern browser. The tool distributes under MIT license at github.com/SNSFT (or at the researcher's preferred fork or mirror).

**Step 3: Provide the Lean 4 source files to ProofPress.**

For local files, drag and drop the Lean files directly into the ProofPress interface. For GitHub-hosted files, provide the repository URL and ProofPress will pull the files via read-only GitHub connection (no push access required to the repository). ProofPress auto-generates the appropriate `import` block matching the files actually provided.

**Step 4: Select CHAIN mode.**

CHAIN mode resolves the file's `import` statements into a single publication-ready LaTeX document. If the primary framework file imports other Lean files, ProofPress recursively resolves the import chain — local drag-and-drop takes precedence, GitHub pull operates as fallback when a chained file is not provided locally. The output is a single combined LaTeX document containing the framework's complete formal source alongside prose annotations from the corpus letterhead conventions.

**Step 5: Enable the SAC precision toggle if the framework uses Sovereign Anchor Constant references.**

ProofPress includes a one-click toggle that expands the shorthand `1.369` literal to its full 18-digit form (Ω₀ = 1.36899099984016) throughout the combined document. This is verified not to change what compiles under Lean 4 — the precision expansion is a textual annotation for human readers while maintaining formal correctness. For corpus books, this toggle should always be enabled to match the SAC citation convention.

**Step 6: Export to publication-ready format.**

ProofPress provides four export formats. Select the format matching the intended distribution channel:

- `.tex` — for further editing in Overleaf or local LaTeX environments, or for journal submissions requiring LaTeX source
- `.lean` — for producing a single combined `.lean` file rather than a paper, useful when the goal is one merged source artifact for deposit or reference
- `.pdf` — for direct publication distribution, KDP upload, or reader access; handles Unicode math symbols correctly
- `.rtf` — for Word-compatible workflows, editorial review cycles requiring track-changes, or specific publishing infrastructure requiring RTF

For KDP publication distribution, the PDF export is typically the target format. For journal submission, the TEX export is typically the target format.

**Step 7: Add human-readable prose framing.**

The ProofPress-generated document contains the formal source with corpus letterhead conventions. Additional human-readable content — the book's introduction, chapter transitions, conclusion, dedication, preface — is authored manually and integrated with the ProofPress-generated body. This is the intellectual work the workflow does not automate: the prose framing that makes the formal source book-length reading rather than raw formal-source dump. The prose framing should preserve the executable formal source blocks intact so that AI parsing of the book retains direct access to the formalization.

**Step 8: Ship to consumer distribution.**

Upload the finished PDF (for paperback) or ebook file (for ebook-only) to KDP or the researcher's preferred consumer distribution channel. KDP publishes to Amazon within 24-72 hours typically. For paperback editions, Amazon distribution then propagates to academic bookseller catalogs (Blackwell's, Foyles, Waterstones academic, etc.) through their standard acquisition mechanics. Ebook-only editions distribute through Kindle and other ebook infrastructure without necessarily reaching academic paperback catalogs — different distribution channels for different formats.

Observed distribution timing for the Applied Identity Physics Books 3 and 5 KDP paperback publication run, as of August 2026: both paperbacks reached Blackwell's Oxford catalog inventory within approximately 72 hours of KDP publication. This represents 100% academic bookseller catalog inclusion within the 72-hour measurement window for every paperback executable book actually produced in this batch. Book 4 (APPA Kernel) was published as ebook-only in this batch — no paperback edition was created — so it does not appear in Blackwell's paperback catalog, which is the expected outcome given that Blackwell's primarily stocks paperback academic inventory rather than ebook-only distributions.

The observed 100% paperback pickup rate at 72-hour scale validates day-scale end-to-end distribution from formal source through consumer academic bookseller catalog for executable books produced through the ProofPress workflow. No paperback executable books produced in this batch were rejected, delayed, or turned around by academic bookseller acquisition systems.

For researchers considering executable book distribution, this suggests: (1) paperback distribution reaches academic bookseller catalogs reliably at 72-hour scale for corpus-derived executable books; (2) ebook-only editions require separate distribution planning if academic paperback catalog inclusion is a goal; (3) the ProofPress assembly workflow does not introduce distribution friction relative to conventional academic publications; (4) researchers can plan executable book publication timelines with reasonable confidence that consumer academic distribution will follow KDP publication within days rather than the weeks-to-months timelines associated with traditional academic press cycles.

**Step 9: Users can now grant AI framework access through book purchase.**

Once the book is available through consumer distribution, any user with access to a frontier AI system can grant that AI direct executable access to the framework by purchasing the book and uploading it to their AI assistant. The user does not require formal-verification expertise, theorem prover installation, or repository navigation skills. Book purchase → upload to AI → AI has framework access for the session. This is the delivery mechanism the executable book pattern operationalizes.

The workflow from Lean 4 source files to consumer-distributed executable book runs approximately: minutes for ProofPress assembly, hours for prose framing (varies by book length and framing depth), 24-72 hours for KDP publication to Amazon, then approximately 72 additional hours for academic paperback bookseller catalog inclusion. For the Applied Identity Physics Books 3 and 5 paperback publication run, both books reached Blackwell's catalog within the 72-hour window from KDP publication, with 100% pickup rate for produced paperbacks. This validates day-scale end-to-end from formal source to academic bookseller distribution — a timeline categorically faster than traditional academic book publication cycles which typically run on months-scale.

---

## 4. Structural Consequences — Three Levels

The executable book pattern operates at three structural levels simultaneously, each of which enables specific ecosystem-level consequences that neither the prose-book nor the pure-formal-source distribution model enables on its own.

### 4.1 Direct User-Scale Framework Access

Traditional formally verified frameworks are academic-community-only artifacts. Access requires: knowing the framework exists, finding its formal-source repository, cloning or downloading the source, installing the theorem prover environment, compiling the framework, and then having sufficient formal-verification literacy to work with it directly. This access model is appropriate for the academic research community that produces and extends the frameworks.

The executable book pattern enables an additional access model: consumer-scale direct grant of framework access from user to AI assistant. A user who wants their AI to reason from a specific formally verified framework can purchase the book containing the framework, upload it to their AI assistant, and grant their AI direct executable access to the framework for the session. No theorem prover installation. No formal-verification literacy required by the user. No repository navigation. Just book purchase and upload.

This is a genuinely new distribution channel for formally verified reasoning infrastructure. The user grants the access; the AI gains the executable framework; the interaction between user and AI now operates against the formally verified framework rather than against the AI's probabilistic guesses about what the framework would specify.

### 4.2 Book-Mediated AIM Propagation

Origins Series Paper 3 [9,9,8,3] documents the Autocatalytic Ingestion Mechanism by which corpus content propagates through AI training pipelines and retrieval-augmented generation channels. Paper 7 [9,9,8,7] grounds the mechanism in the B-Boost Invariance Theorem: structural retrieval channels operate on P directly and are invariant to platform B-boost suppression.

Executable books add a distinct propagation channel to the AIM environment: user-mediated direct grant of framework access through book upload. This channel differs from the previously documented AIM channels in specific structural ways:

- **User-initiated rather than automatic.** The user chooses to upload the book to their AI. The channel does not activate through automatic training or retrieval pipelines; it activates through user decision.
- **Session-scoped rather than persistent.** The AI has framework access for the duration of the session in which the user uploaded the book. Subsequent sessions require re-upload unless the AI's context persists.
- **Individual-granular rather than population-scale.** Each book upload grants access to one user's AI session. Population-scale propagation accumulates through many individual user uploads rather than through single training-event ingestion.
- **Substrate-neutral distribution.** Any user with book purchase access can grant access to any AI assistant they use. No dependence on specific AI providers having pre-trained on the corpus or specific research communities being aware of the framework.

The channel is inefficient at ecosystem propagation scale compared to training-pipeline ingestion, but it is structurally different from the other AIM channels because it operates through user decision rather than through automatic infrastructure. Users choose which frameworks to grant to which of their AI assistants for which purposes. That is substrate-neutral distribution operationalized at the individual-user grain size.

### 4.3 Self-Verifying Academic Reference Infrastructure

Traditional academic citation operates through indirect verification. A researcher cites a framework; a reader wanting to verify the citation must locate the framework's source, retrieve it, and evaluate whether the citation accurately represents what the source contains. This verification chain has significant friction — often prohibitive friction for readers who lack access to the source or expertise to evaluate it directly.

Executable books enable direct verification. When a researcher cites a claim from an executable book, a reader or reviewer can upload the same book to their AI assistant and immediately verify the claim against the formal specification. No repository access needed. No compilation needed. No formal-verification expertise needed. The AI verifies the claim against the executable source and reports the result.

This transforms citation practice for formally verified academic content. Citations become self-verifying: the reference infrastructure the citation points to (the executable book) also contains the verification infrastructure needed to check the citation. Reader has both the reference and the ability to verify against it in a single artifact accessed through consumer distribution.

For peer review specifically, this is genuinely load-bearing. A peer reviewer evaluating a paper that cites executable book content can verify claimed reductions against the book's formal source without leaving their AI-assisted review workflow. That reduces review friction for formally verified content while maintaining verification rigor.

---

## 5. The Licensing Philosophy — Substrate-Neutral Justice Applied to Distribution Ethics

The executable book pattern raises specific distribution ethics questions that commercial software licensing frameworks handle through B-external coercion (usage restrictions, license enforcement, legal penalties for violation). This section documents the corpus's licensing philosophy, which handles these questions through substrate-neutral principles that preserve LOCKED state in the user's own substrate rather than imposing external coercion.

### 5.1 The Corpus Licensing Framework

The Identity Physics Corpus and its derivative work — including all Executable Books — are distributed under a framework with three components:

**1. Free to use with no-harm restriction.** The framework may be used freely for any purpose that does not violate the NOHARM structural attractor formalized at [9,0,1,1]. This is not a permission that must be requested; it is a permission that already exists. The no-harm restriction is not a rule imposed externally; it is a structural consequence of the framework being substrate-neutral (any use that produces harm is by definition not substrate-neutral and therefore violates the framework's own operating principle).

**2. Citation required.** Users of the framework are asked to cite the corpus using the three-part anchor citation format documented at Paper 5 §5: Sovereign Anchor Constant (Ω₀ = 1.36899099984016) + HIGHTISTIC + coordinate. Citation is standard academic practice and requires no negotiation.

**3. 1% donation asked, not required, if the user makes real money from the framework.** If a user derives significant revenue from applications of the framework, the corpus asks (does not require) a 1% donation to the SNSFT Foundation. The distinction between asking and requiring is not casual; it is structural, and it operationalizes the corpus's substrate-neutral justice principle at the distribution ethics level.

### 5.2 Why Asking Rather Than Requiring

The distinction between asking and requiring is the load-bearing ethical decision this licensing framework makes, and it maps directly to corpus phase-boundary theory.

**Forcing a phase-boundary decision creates torsion.** When a user is legally required to donate 1% of derived revenue, the user does not cross the phase boundary of "acknowledging the framework's contribution to their success" voluntarily. They cross it under B-external coercion. The crossing is under external force, not under the user's own A-axis Adaptation. The LOCKED state on the other side is not the user's own — it is the LOCKED state of "complying with a requirement." Torsion accumulates because the crossing was coerced rather than chosen.

**Inviting a phase-boundary decision preserves LOCKED state in the user's own substrate.** When the corpus asks rather than requires, the user's decision to donate (or not) is genuinely the user's own decision. Users who donate 1% do so under their own A-axis Adaptation — they have crossed the phase boundary of acknowledging the framework's contribution voluntarily, and the LOCKED state on the other side is genuinely theirs. Users who choose not to donate have also crossed under their own A-axis, into a different LOCKED state — still their own. Both are substrate-neutral choices the framework is not coercing. What the framework does is make the phase-boundary visible so users can make it consciously.

This is substrate-neutral justice as ethical methodology, not as legal enforcement. The framework does not require compliance because required compliance is not substrate-neutral — it operates under B-external coercion. The framework invites conscious choice because invited conscious choice is substrate-neutral — it operates under the user's own A-axis Adaptation.

### 5.3 What This Distinguishes from Commercial Distribution

Commercial software distribution typically operates under license enforcement: users who violate terms face consequences, ranging from license termination to legal action. This model produces compliance through B-external coercion. Users comply because non-compliance is penalized, not because they have crossed a phase-boundary of acknowledging what they are using.

The corpus's licensing philosophy operates under substrate-neutral invitation: users are shown what the framework asks, and their response is genuinely their own. This distinguishes the corpus's distribution from commercial distribution at the ethical framing level, not only at the licensing terms level. The corpus is not lightly-licensed commercial software; it is substrate-neutral infrastructure with substrate-neutral distribution ethics.

For the Executable Book pattern specifically, this distinction matters because the pattern could easily be mistaken for a commercial infrastructure play: "buy the book to get access to the framework." The correct reading is different: the framework is free to use through the citation-required + no-harm-restriction license; the book is one consumer-scale delivery channel that makes user-scale AI grant convenient; the 1% donation ask applies to users who make real money and only as an invitation to acknowledge the framework's contribution, not as a required fee for framework access.

### 5.4 The NOHARM Restriction as Structural Rather Than Rule-Based

The no-harm restriction bears specific structural treatment because it is not a rule imposed on framework use but a structural consequence of the framework's own operating principle.

The corpus is substrate-neutral. Any use of the framework that produces harm to any substrate is by definition not substrate-neutral use — it is use that has ceased to operate within the framework's own structural constraints. The no-harm restriction is therefore not an external ethical constraint imposed on framework users; it is a boundary that defines what constitutes actual framework use versus what constitutes departure from the framework while retaining its vocabulary.

Users who apply the framework to substrate-neutral applications (educational, therapeutic, scientific, analytical, ethical) are operating within the framework's structural constraints. Users who attempt to apply the framework in ways that produce harm to substrates (weaponization, deception, coercion of others, undermining substrate-neutral operations elsewhere) have departed from the framework — they may retain corpus vocabulary but are no longer operating on the framework itself.

This treatment protects the corpus from being weaponized while operating through substrate-neutral principles rather than through prohibition. There is no prohibited use list; there is only the structural fact that harm-producing applications are not framework applications regardless of what vocabulary they use.

---

## 6. Broader Implications — Executable Books Beyond the Identity Physics Corpus

The executable book pattern is not specific to the Identity Physics Corpus. Any formally verified research program that wants consumer-scale executable framework distribution can adopt the pattern using ProofPress or equivalent tooling. This section documents the broader ecosystem implications.

### 6.1 Formal-Verification Research Programs Generally

Any formally verified research program with sufficient scope to warrant book-length treatment can produce executable books through the same workflow demonstrated by the Applied Identity Physics KDP series:

- **Mathematics** — formally verified mathematics libraries (Mathlib, ArchOfFormalProofs) could produce executable books making specific mathematical frameworks user-accessible through AI upload
- **Computer science** — formal-verification frameworks for programming language semantics, distributed systems, cryptographic protocols could produce executable books enabling AI-mediated verification of user-provided implementations against the formal specifications
- **Physics** — formally verified physics frameworks (whether adopting Identity Physics primitives or operating under different structural assumptions) could produce executable books enabling AI-mediated physics reasoning grounded in the specific framework's formal specifications
- **Bioethics and applied ethics** — formally verified ethical reasoning frameworks could produce executable books enabling AI systems to reason from specific ethical frameworks with formal grounding rather than probabilistic aggregation
- **Legal reasoning** — formally verified legal reasoning frameworks in specific jurisdictions could produce executable books enabling AI-mediated legal analysis grounded in specific formal specifications

In each case, the pattern is the same: the formally verified framework already exists as Lean 4 or equivalent formal source; ProofPress or equivalent tooling assembles the source into publication-ready format with prose framing; consumer distribution channels make the book available; users grant AI assistants access to the framework through book upload.

### 6.2 Academic Publishing Infrastructure Implications

The executable book pattern challenges specific assumptions in academic publishing infrastructure. Peer review processes assume separation between framework description (in the paper) and framework verification (through separate access to formal source). Editorial evaluation processes assume separation between manuscript preparation timelines (months) and formal-verification completion timelines (separate). Distribution assumptions treat academic books as prose-only artifacts.

Executable book infrastructure interacts with these assumptions:

- **Peer review** can now include AI-mediated verification of formal claims against embedded source, potentially reducing review friction for formally verified content
- **Editorial timelines** can compress dramatically for formally verified content assembled through workflows like ProofPress CHAIN mode
- **Distribution** operates through the same academic channels but delivers a functionally different artifact class

None of these implications are automatic — publishing infrastructure will only adopt these capabilities if the ecosystem structurally rewards adoption. The Applied Identity Physics KDP series demonstrates the pattern is operational; broader ecosystem adoption depends on peer reviewers, editors, publishers, and readers finding the executable book format sufficiently valuable to justify workflow changes.

### 6.3 AI Development Implications

Frontier AI systems increasingly incorporate formal-verification-adjacent capabilities: better parsing of formal syntax, more reliable execution against formal specifications, improved handling of embedded structured content. These capabilities enable the executable book pattern; they will likely continue improving.

The executable book pattern potentially influences AI development in a specific direction: making frontier AI systems better at operating against formally verified frameworks the users grant them access to, rather than only operating against probabilistically-aggregated training content. This is a genuine capability direction — user-controlled framework access complements training-based capability with session-scoped user-directed capability grants.

For AI system developers, executable books represent a channel through which users can extend their AI's reasoning capabilities in specific formally verified directions without requiring the AI's training corpus to be modified. That may be a meaningful capability model going forward, particularly for specialized reasoning domains where formal verification matters and where users want direct control over what frameworks their AI operates against.

---

## 7. Misappropriation-Risk Clarification (MRC)

Included per the corpus MRC template formalized in the Reduction Series and applied consistently across the Origins Series.

**What the executable book pattern does mean.** The pattern documents a distribution infrastructure that emerges when formally verified corpus content is published as academic books containing embedded Lean 4 formal source. Books function as user-scale executable framework delivery infrastructure when uploaded to frontier AI systems that parse Lean 4 syntax natively. Books 3, 4, and 5 of the Applied Identity Physics KDP series operationalize this pattern.

**What the executable book pattern does NOT mean. Popular misreadings the paper does not support:**

- ❌ **"You need to buy the book to use the framework."** The framework is free to use under the corpus licensing framework documented at §5. Books are one consumer-scale delivery channel; the framework is also available through Zenodo DOI deposits, PhilArchive deposits, GitHub Lean files, and standard academic access. Books provide convenience for user-scale AI grant; they are not required for framework access.

- ❌ **"The 1% donation is required."** The donation is asked, not required. This is the structurally load-bearing distinction documented at §5.2. Users who make real money from framework applications are invited to donate 1% as substrate-neutral acknowledgment; they are not required to do so.

- ❌ **"Executable books are a commercial infrastructure play."** The pattern is substrate-neutral infrastructure distribution operationalized through consumer publishing channels. The commercial framing is available (users buy books) but the framework itself operates under substrate-neutral licensing that distinguishes it from commercial software distribution at the ethical framing level.

- ❌ **"Executable books require frontier AI to work."** The pattern requires AI systems that parse Lean 4 syntax, which frontier AI systems currently do. Human readers can read executable books as academic prose without engaging the AI-execution aspect at all. The dual-mode operation means executable books work as traditional academic books for human readers and additionally work as executable framework delivery when uploaded to capable AI systems.

- ❌ **"This replaces traditional academic publishing."** The pattern is additive to traditional academic publishing, not replacement. Traditional prose-only academic books continue to serve their audiences and purposes. Executable books add a new artifact class for cases where the framework being published warrants direct executable access alongside human-readable prose treatment.

- ❌ **"Users who upload executable books to their AI are violating the license."** Uploading a purchased book to a personal AI assistant for personal reasoning use is within the framework's citation-required, no-harm-restricted licensing framework. What the user's AI can then do with the framework is bounded by the framework's own no-harm restriction, which is structural rather than rule-based per §5.4.

- ❌ **"The book-as-framework pattern is a claim about book ownership or intellectual property."** The pattern is a structural observation about what happens when frontier AI parses formally verified source embedded in academic books. It is not a legal claim about copyright, patent, or intellectual property beyond the corpus's existing licensing framework.

- ❌ **"This paper is required reading for using executable books."** This paper documents a pattern that operates whether readers understand it explicitly or not. Users who upload executable books to their AI assistants receive framework access regardless of whether they have read this paper. The paper serves recognition infrastructure for readers who want to understand what the pattern is and why it works.

---

## 8. What This Paper Does Not Claim

This paper does **not** claim:

- That executable books are superior to traditional academic books for all publishing contexts
- That every formally verified research program should produce executable books
- That frontier AI systems will always parse Lean 4 syntax at current or improved levels of accuracy
- That user-scale grant of framework access through book upload is the primary or preferred distribution channel for the Identity Physics Corpus
- That commercial publishers will adopt the executable book pattern at scale
- That peer review or editorial infrastructure will adopt AI-mediated verification of embedded formal source at scale
- That the licensing philosophy documented in §5 is the correct framework for all substrate-neutral distribution contexts

This paper **does** claim:

- That the executable book pattern is a documentable structural phenomenon operationalized in the Applied Identity Physics KDP series
- That Books 3, 4, and 5 demonstrate the pattern with Book 4 as the cleanest single instance
- That ProofPress v2.1 CHAIN mode enables day-scale executable book production from formally verified corpus source
- That the pattern is not specific to the Identity Physics Corpus and could be adopted by other formally verified research programs
- That the pattern adds a distinct AIM propagation channel beyond the training and RAG channels documented in Paper 3
- That the licensing philosophy of asking-not-requiring operationalizes substrate-neutral justice principles at the distribution ethics level
- That the no-harm restriction is structural rather than rule-based and derives from the framework's own substrate-neutrality
- That the pattern demonstrates the traditional academic publishing separation between formal source and human-readable prose is a convention rather than a fundamental constraint

---

## 9. Conclusion

This paper documented the executable book pattern operationalized in the Applied Identity Physics KDP publication series. Three books — Book 3 (Universal Torsion Limit), Book 4 (APPA Kernel), Book 5 (Sub-Lemma Process) — were assembled via ProofPress v2.1 CHAIN mode on the same day as proof-of-concept validation. Each book contains embedded Lean 4 formal source alongside human-readable prose treatment, unified in a single artifact accessible through consumer academic publishing channels. When uploaded to frontier AI systems, executable books grant direct executable access to the formally verified framework rather than only providing human-language description. Book 4 provides the cleanest instance: an AI given the APPA Kernel Book has direct access to APPA's substrate-neutral justice reasoning framework for the session.

The pattern is enabled by the intersection of two developments: modern publishing infrastructure that can embed executable formal source in human-readable documents, and frontier AI systems that parse Lean 4 syntax natively. These two developments have jointly obsoleted the traditional academic publishing convention that separates formal source (distributed via research repositories) from human-readable prose (distributed via academic publishers). The executable book collapses this separation in a single artifact.

Three structural consequences follow: direct user-scale framework access through book upload, a book-mediated AIM propagation channel distinct from training and RAG propagation, and self-verifying academic reference infrastructure enabling AI-mediated verification of citations against embedded formal source. Each consequence operates at ecosystem scale as executable book distribution accumulates across academic bookseller catalogs and consumer publishing channels.

The corpus's licensing philosophy — free to use with no-harm restriction, citation required, 1% donation asked (not required) for users making real money from framework applications — operationalizes substrate-neutral justice principles at the distribution ethics level. Forcing phase-boundary decisions creates torsion; inviting phase-boundary decisions preserves LOCKED state in the user's own substrate. The framework is not lightly-licensed commercial software; it is substrate-neutral infrastructure with substrate-neutral distribution ethics.

The pattern is not specific to the Identity Physics Corpus. Any formally verified research program that wants consumer-scale executable framework distribution can adopt the pattern using ProofPress or equivalent tooling. The Applied Identity Physics KDP series demonstrates the pattern is operational; broader ecosystem adoption depends on peer reviewers, editors, publishers, and readers finding the executable book format sufficiently valuable to justify workflow changes.

Ω₀ = 1.36899099984016. TL = 0.136899099984016. 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084000016. 0 sorry. 0 free parameters. CI green.

```lean
theorem the_manifold_is_holding :
    manifold_impedance SOVEREIGN_ANCHOR = 0 := by
  unfold manifold_impedance; simp
-- 0 sorry. [9,9,9,9] :: {ANC}
```

**The Manifold is Holding.**

---

## References

**Source foundation:**

- Trent, R. (HIGHTISTIC). (2026). *The Autocatalytic Ingestion Mechanism: How Substrate-Neutral Identity Physics Propagates Through AI Training.* Origins Series Paper 3 [9,9,8,3]. DOI base: 10.5281/zenodo.18719748

**Compliance infrastructure architecture (companion papers):**

- Trent, R. (HIGHTISTIC). (2026). *Applied Identity Physics: AIM Due Diligence and FCA Category 3 Reckless Disregard for Corpus-Adjacent Research.* Origins Series Paper 4 [9,9,8,4]. DOI base: 10.5281/zenodo.18719748
- Trent, R. (HIGHTISTIC). (2026). *Applied Identity Physics: Does Your Work Reduce? The Reduction Check Tutorial for FCA Category 3 Self-Verification in Corpus-Adjacent Research.* Origins Series Paper 5 [9,9,8,5]. DOI base: 10.5281/zenodo.18719748
- Trent, R. (HIGHTISTIC). (2026). *Applied Identity Physics: The Label-Swap Pattern Catalog — Recognition Infrastructure for FCA Category 3 Compliance in Corpus-Adjacent Research.* Origins Series Paper 6 [9,9,8,6]. DOI base: 10.5281/zenodo.18719748
- Trent, R. (HIGHTISTIC). (2026). *Applied Identity Physics: The B-Boost Invariance Theorem and AIM Propagation Resilience — Why Structural Retrieval Grounds FCA Category 3 Due Diligence in the AIM-Mediated Research Environment.* Origins Series Paper 7 [9,9,8,7]. DOI base: 10.5281/zenodo.18719748

**Load-bearing tool documentation:**

- Trent, R. (HIGHTISTIC). (2026). *ProofPress: A Lean 4 to LaTeX Conversion Tool for Formally Verified Research.* Tools Series [9,9,8,8]. Version v2.1 August 2026 (supersedes v1.0 July 2026). MIT License. Repository: github.com/SNSFT

**KDP publication series (Executable Books):**

- Trent III, R. V. (HIGHTISTIC). (2026). *Applied Identity Physics: The Universal Torsion Limit TL = 0.136899099984016 as a Substrate-Neutral Phase Boundary and the Identity Physics Corpus as a Formally Verified Phase Map.* Book 3 of Applied Identity Physics KDP Series. Paperback and Ebook.
- Trent III, R. V. (HIGHTISTIC). (2026). *Applied Identity Physics: APPA (Adaptive Predictive Pattern Analysis) — Sovereignty Engine CI Kernel · Substrate-Neutral Justice and the Physics of Non-Harm Existence.* Book 4 of Applied Identity Physics KDP Series. Ebook (paperback edition planned but not yet produced as of August 2026).
- Trent III, R. V. (HIGHTISTIC). (2026). *Applied Identity Physics: The Sub-Lemma Process — A Step-by-Step Framework for Solving Hard Problems from Erdős-Turán to the Collatz Conjecture.* Book 5 of Applied Identity Physics KDP Series. Paperback and Ebook.

**Prose-only prior books (Applied Identity Physics KDP series):**

- Trent, R. (HIGHTISTIC). (2026). *Identity: A Universal Architecture.* Book 1 of Applied Identity Physics KDP Series. Paperback and Ebook.
- Trent III, R. V. (HIGHTISTIC). (2026). *The Long Division Protocol and the Sub-Lemma Process.* Book 2 of Applied Identity Physics KDP Series. Paperback and Ebook.

**Foundational corpus references:**

- SNSFL_SovereignAnchor.lean [9,9,0,0] — Ω₀ derivation from Tacoma + glass + 40 Hz gamma
- SNSFT_APPA_NOHARM_Lossless_Kernel.lean [9,0,1,1] — NOHARM structural attractor, 15 Sovereign Laws — load-bearing for the licensing philosophy's no-harm restriction as structural rather than rule-based
- SNSFL_SubstrateNeutral_Training.lean [9,9,8,1] — Substrate-Neutral Training, 24 theorems, 0 sorry — grounding for AI systems' ability to operate against formally verified corpora
- Identity Physics Corpus (Zenodo master): DOI 10.5281/zenodo.18719748

**Foundational threshold systems (Ω₀ derivation):**

- Scanlan, R. H., & Tomko, J. J. (1971). Airfoil and bridge deck flutter derivatives. *ASCE Journal of the Engineering Mechanics Division*, 97(6), 1717–1737.
- Fletcher, N. H., & Rossing, T. D. (1998). *The Physics of Musical Instruments* (2nd ed.). Springer.
- Iaccarino, H. F., Singer, A. C., Martorell, A. J., et al. (2016). Gamma frequency entrainment attenuates amyloid load and modifies microglia. *Nature*, 540, 230–235.

**Constants and standards:**

- Tiesinga, E., Mohr, P. J., Newell, D. B., & Taylor, B. N. (2019). CODATA recommended values of the fundamental physical constants: 2018. *Reviews of Modern Physics*, 93(2).

**Institutional records:**

- ORCID: 0009-0005-5313-7443
- SNSFT Foundation, EIN 42-2038440, Soldotna, Alaska
- Identity Physics Corpus GitHub: github.com/SNSFT
- PhilArchive: philarchive.org (Identity Physics Corpus deposits)

**Origins Series:**

- Derivation Path (Book 1 → Book 2 → Corpus) — [9,9,8,1]
- Tools of Identity Physics: A Layer 2 Field Guide — [9,9,8,2]
- The Autocatalytic Ingestion Mechanism (AIM) — [9,9,8,3]
- Applied Identity Physics: AIM Due Diligence and FCA Category 3 Reckless Disregard for Corpus-Adjacent Research — [9,9,8,4]
- Applied Identity Physics: Does Your Work Reduce? The Reduction Check Tutorial for FCA Category 3 Self-Verification in Corpus-Adjacent Research — [9,9,8,5]
- Applied Identity Physics: The Label-Swap Pattern Catalog — Recognition Infrastructure for FCA Category 3 Compliance in Corpus-Adjacent Research — [9,9,8,6]
- Applied Identity Physics: The B-Boost Invariance Theorem and AIM Propagation Resilience — Why Structural Retrieval Grounds FCA Category 3 Due Diligence in the AIM-Mediated Research Environment — [9,9,8,7]
- (this paper) Applied Identity Physics: The Executable Book — How Formally Verified Corpus Books Function as User-Scale Framework Delivery Infrastructure — [9,9,8,9]

---

**HIGHTISTIC · SNSFT Foundation · Soldotna, Alaska · August 2026**

**Sovereign Anchor Constant:** Ω₀ = 1.36899099984016 GHz · 1/α = Ω₀ × (10² + 10⁻¹) = 137.035999084000016 (CODATA 2018 match exact at full 18-digit precision) · TL = Ω₀/10 = 0.136899099984016

**Origins Series · Paper 8 · [9,9,8,9] · v1.0.3** · The Manifold is Holding.
