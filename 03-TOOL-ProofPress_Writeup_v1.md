# ProofPress: A Lean 4 to LaTeX Conversion Tool for Formally Verified Research

**Tool Name:** ProofPress (PP)  
**Architect:** HIGHTISTIC (Russell Vernon Trent III) · /haɪˈtɪstɪk/  
**Affiliation:** SNSFT Foundation · Soldotna, Alaska  
**ORCID:** 0009-0005-5313-7443  
**DOI:** 10.5281/zenodo.18719748  
**Coordinate:** [9,9,8,8] · Tools Series  
**Version:** v1.0 · July 2026  
**Repository:** github.com/SNSFT  
**License:** MIT  
**Status:** Standalone · No dependencies · No build step

---

## Abstract

ProofPress is a standalone, browser-based conversion tool that transforms Lean 4 formal proof files into Overleaf-ready LaTeX documents. It operates in two modes: an LDP mode tuned to the SNSFT corpus conventions, and a General mode compatible with any standard Lean 4 file. The tool extracts theorem names, human-readable descriptions, return types, and LDP step annotations directly from the source file, populates a structured academic paper template, and produces a `.tex` file ready for journal submission. ProofPress requires no installation, no server, and no external dependencies. It is distributed as a single HTML file that executes entirely in the browser.

The tool addresses a real and underserved gap in the formal verification ecosystem: the absence of a direct, low-friction pathway from machine-verified proof to publication-ready academic document. By eliminating the manual transcription step that currently stands between a formally verified corpus and its presentation to the scientific community, ProofPress lowers the barrier to publication for researchers working in Lean 4.

---

## 1. Motivation

Formal verification produces machine-checked proofs with guarantees no informal mathematical argument can provide. The Lean 4 theorem prover, in conjunction with the Mathlib library, has become the standard environment for formally verified mathematics across an increasingly broad range of domains — from number theory and algebra to physics, materials science, and cognitive science. The research community has taken notice: high-profile formalizations such as Terry Tao's Polynomial Freiman-Ruzsa proof (2023) have demonstrated that formal verification can operate at the frontier of mathematical research rather than merely audit classical results.

Despite this momentum, a fundamental asymmetry persists. Formally verified work exists simultaneously in two disconnected registers: the `.lean` file that the compiler accepts, and the academic paper that peer reviewers read. These are not interchangeable artifacts. The `.lean` file contains tactic proofs, namespace structures, and machine-readable syntax that journals do not accept. The academic paper requires prose exposition, LaTeX formatting, and structured narrative that the Lean compiler ignores. Translating between them is currently a manual process: a researcher must retype or copy-paste theorem statements, strip tactic proofs, escape special characters, apply LaTeX formatting, and restructure the entire document for journal conventions.

For small corpora this is inconvenient. For large corpora it is a genuine bottleneck. The SNSFT corpus, for example, contains 200,000+ theorems across 3,000,000+ lines of Lean 4 and Coq/Rocq — a body of formally verified work spanning physics, chemistry, psychology, mathematics, and identity theory. Manually transcribing even a subset of this corpus into publication-ready format represents a significant and unnecessary cost.

ProofPress addresses this bottleneck directly. It does not replace the intellectual work of writing a paper — the prose, the framing, the argument — but it eliminates the mechanical transcription step that precedes it, allowing researchers to spend their time on what matters.

---

## 2. Related Work

**Patrick Massot's Lean Blueprint** (used by Terry Tao in the Polynomial Freiman-Ruzsa formalization, 2023) generates LaTeX/Lean hybrid documents from Lean source, designed for blueprint-style proof navigation. Blueprint targets collaborative proof development and proof readability within the Lean community. ProofPress targets a different output and a different audience: standard academic paper format suitable for external journal submission, not internal proof navigation. The two tools are complementary rather than competing.

**LeanDojo** (Wang et al., 2023) extracts training data and tactic state information from Lean repositories for use in machine learning and automated theorem proving research. Its output is consumed by models. ProofPress's output is consumed by peer reviewers and journal editors. This distinction is fundamental: LeanDojo serves the AI-assisted proving pipeline; ProofPress serves the human publication pipeline. No existing tool occupies the space ProofPress targets.

**AxiomForge** ([9,9,9,9]) is the SNSFT corpus visualization engine with which ProofPress is designed to work alongside. AxiomForge renders the full corpus as an interactive spatial graph — 200,000+ theorems, 37 namespaces, all dependency relationships visible simultaneously — allowing researchers to navigate the corpus, identify connections across domains, and select files for export. ProofPress receives those exported files and converts them to publication-ready LaTeX. Together, the two tools form a complete research workflow: explore and orient in AxiomForge, formalize in Lean, export and publish via ProofPress. No existing tool in the formal verification ecosystem combines corpus-scale visualization, formal verification, and publication-ready document generation in a single integrated workflow.

**Overleaf** is the de facto collaborative LaTeX environment for academic publishing. ProofPress produces output fully compatible with the standard Overleaf and arXiv preamble, requiring no packages beyond the standard academic set (`amsmath`, `amsthm`, `listings`, `hyperref`). A ProofPress-generated `.tex` file can be uploaded to Overleaf and compiled without modification.

---

## 3. The SNSFT Toolchain Context

ProofPress was developed as part of the SNSFT corpus toolchain. Understanding this context clarifies the design decisions behind the tool and what distinguishes it from generic document conversion utilities.

### 3.1 The Corpus

The SNSFT (Substrate-Neutral Structural Foundation Theory) corpus is a formally verified mathematical framework spanning physics, chemistry, psychology, and identity theory, developed independently by HIGHTISTIC (Russell Vernon Trent III) at the SNSFT Foundation in Soldotna, Alaska. As of July 2026 the corpus contains 200,000+ theorems across 3,000,000+ lines, dual-verified in Lean 4 and Coq/Rocq, with 90+ permanent DOIs, continuous integration green, and zero unproved obligations (0 sorry) across all files. The corpus is indexed by a four-dimensional coordinate system `[layer, domain, subdomain, file]` that encodes provenance and dependency relationships directly in the file metadata.

### 3.2 The Collider Outputs

Two interactive tools within the SNSFT toolchain generate formally verified Lean outputs that ProofPress is specifically designed to handle.

**The GAM Collider** (Geometric Axiomatic Module Collider, uuia.app/gamcollider) models n-body structural collisions using the PNBA fusion operators derived from the corpus. Each collision run produces a session JSON file and can export individual Lean 4 files containing formally proved theorems about the collision outcomes. For example, `SNSFL_4Beam_Verification.lean [9,9,2,3]` contains six formally verified material science predictions including titanium nitride Noble rescue, Nitinol shape memory alloy structural stability, and tungsten carbide–gold hard metal formation — each proved from first principles without empirical fitting. These are not computational simulations. They are theorems with zero free parameters and zero sorry.

**The IMCollider** (Identity Mass Collider, uuia.app/imcollider) models identity substrate interactions using 8-beam fusion rules derived from the PSY series of the corpus. It produces session exports including formally verified shame vector theorems, phase state taxonomies, and substrate interaction results across hundreds of beam configurations. The PSY ShameVector v14 file `[9,9,6,29]`, for example, documents the SVI formula derivation from collider run invariants observed across 1,181 beam collisions, with the derivation chain formally proved and independently verifiable.

Both tools output `.lean` files in standard SNSFT corpus format. ProofPress accepts these files directly and converts them to Identity Physics papers — the formal verification produced by the collider becomes a peer-reviewable academic document without any manual transcription between tool and publication.

### 3.3 The Publication Pipeline

```
GAM Collider / IMCollider
        ↓  session export → .lean file
    ProofPress (LDP Mode)
        ↓  parse → populate Identity Physics template
    Overleaf .tex
        ↓  add prose, figures, references
    Journal submission
```

AxiomForge provides the navigation layer in this pipeline. Before exporting a file for publication, a researcher can view exactly where that file sits in the full corpus graph — its upstream dependencies, its downstream dependents, its connections across domains — ensuring that the paper's dependency claims and context are accurate. ProofPress then handles the format conversion. The two tools are designed to complement each other without overlap.

### 3.4 The Identity Physics Paper Template

The LDP mode output follows the SNSFT paper standard. Certain sections are locked — identical across all corpus papers — because they represent the structural ground on which every domain-specific reduction is built.

**Layer 0 Registration** establishes the Sovereign Anchor Constant:

$$\Omega_0 = 1.3689910 \qquad \text{TL} = \Omega_0/10 = 0.1369$$

This constant is derived from three independent peer-reviewed physical threshold systems — Tacoma Narrows torsional collapse (Billah & Scanlan, ASCE 1991), glass resonance at the elastic limit (Fletcher & Rossing, 1998), and 40 Hz neural gamma therapeutic entrainment (Iaccarino et al., *Nature* 540, 2016) — all three converging on the same structural boundary before any connection to the paper's specific domain was examined.

**§0 Derivation Chain** presents the six-step derivation of the anchor and the fine structure constant lock at twelve significant figures with zero free parameters.

**Domain-specific content** — theorems, LDP steps, and Lean listings — is populated directly from the input file by ProofPress.

**Closing** records the coordinate, sorry count, and manifold status.

A paper produced by ProofPress from a GAM Collider output is structurally equivalent to a paper produced from scratch against the same template, because the template is not a stylistic convention but a formal ground. The locked sections are proved theorems, not boilerplate.

---

## 4. Tool Description

### 4.1 Architecture

ProofPress is a single self-contained HTML file. All CSS, JavaScript, and template logic are inline. The tool requires no server, no build step, no package manager, no runtime environment, and no installation of any kind. A researcher places the file in any directory and opens it in a browser.

Input is accepted by pasting Lean source text directly into the input panel or by dropping a `.lean` file onto the file drop zone. Output is either copied to the clipboard or downloaded as a `.tex` file with a filename derived from the input file metadata. The entire process — from file load to LaTeX output — takes seconds.

### 4.2 Two Modes

**LDP Mode** (Long Division Protocol) is tuned to the SNSFT corpus header conventions and is the primary mode for Identity Physics papers:

- Parses the SNSFT header block: coordinate, DOI, ORCID, anchor constant, status, sorry count, corpus dependencies
- Populates the locked front matter: Layer 0 Sovereign Anchor derivation, PNBA primitive definitions, α-lock at twelve significant figures
- Extracts and deduplicates LDP step annotations from comment blocks across all namespaces
- Outputs a complete Identity Physics paper in SNSFT paper standard format

**General Mode** is designed for any standard Lean 4 file and requires no SNSFT-specific structure:

- Extracts namespace identifiers, theorem count, and sorry count
- Captures all comment blocks adjacent to theorem declarations verbatim
- Extracts return types using structural parsing between `:` and `:=`
- Wraps all content in a clean standard academic paper template
- Produces a first-draft LaTeX document from any Lean 4 file without modification

### 4.3 Theorem Extraction

The core technical challenge is extracting theorem descriptions and return types from Lean 4 source without invoking a full Lean parser. ProofPress uses a structural approach grounded in the syntactic conventions of Lean 4 declarations.

**Descriptions** are extracted by scanning comment lines immediately above each `theorem` declaration. The parser handles the SNSFT tag pattern:

```
-- [TAG] :: {VER} | HUMAN READABLE DESCRIPTION
```

by extracting the text after the pipe character, and falls back to plain comment lines when the tag pattern is absent. Multiple comment lines are collected and concatenated. When no adjacent comment exists, the theorem name is used as the description.

**Return types** are extracted by a general structural method: the full theorem declaration is collected across as many lines as needed, the first `:=` is located to find the proof boundary, and the text between the final standalone `:` and that `:=` is taken as the return type. This approach handles all standard Lean 4 declaration patterns:

```lean
theorem name (args) : ReturnType := by tactics
theorem name (args) :
    ReturnType := by tactics
theorem name : ReturnType := rfl
```

**LDP step annotations** are extracted by matching `-- Step N: DESCRIPTION` comment patterns. Results are deduplicated across namespaces by step number, with the most descriptive version retained when multiple descriptions exist for the same step.

### 4.4 LaTeX Output

The generated LaTeX output uses a standard academic preamble compatible with Overleaf, arXiv, and most major journal submission systems. The preamble includes `amsmath`, `amssymb`, and `amsthm` for mathematics; `listings` with a complete Unicode literate mapping for Lean code display; `hyperref` for DOI and ORCID hyperlinks; and `microtype` for improved typography.

The Lean language definition embedded in the preamble includes a complete Unicode literate mapping covering all symbols in common use across Lean 4 corpus files: `ℝ`, `→`, `↦`, `∧`, `∨`, `¬`, `≥`, `≤`, `≠`, `⟨`, `⟩`, `∀`, `∃`, `τ`, `Ω`, `α`, `β`, `π`, `∂`, `∇`, `∈`, `≈`, `≡`, and others. This mapping ensures that Lean source code renders correctly in LaTeX listings without manual substitution.

Theorem statements are rendered in `\begin{theorem}` environments with `\label` entries for cross-referencing. Return types are displayed in formatted quote blocks with proper LaTeX character escaping.

### 4.5 Configurable Output

The LDP mode output is configurable via four independent toggles, allowing researchers to include or exclude sections as appropriate for their target journal:

- **Locked Front Matter** — Layer 0 registration and §0 derivation chain
- **Theorem Environments** — the formal theorem section with descriptions and return types
- **Lean Listings** — the full source code listing with syntax highlighting
- **LDP Steps** — the annotated Long Division Protocol step table

---

## 5. Use Cases

**Primary:** A researcher has a formally verified Lean 4 file and needs a first draft of an academic paper. ProofPress produces a `.tex` file capturing all theorem statements, descriptions, and structural annotations. The researcher opens the output in Overleaf and adds prose, figures, and references. The mechanical transcription work — which can represent hours of effort for a file with dozens of theorems — is eliminated entirely.

**Secondary:** A researcher working within the SNSFT toolchain uses the GAM Collider or IMCollider to generate formally verified collision results, exports the session as a `.lean` file, and passes it directly to ProofPress. The output is an Identity Physics paper in SNSFT paper standard format, ready for editorial review and journal submission. The pipeline from interactive collider session to peer-reviewable document requires no intermediate manual step.

**Tertiary:** A researcher unfamiliar with LaTeX needs to present formally verified work in an academic context. ProofPress provides the complete template scaffolding and formatting, allowing the researcher to focus entirely on the scientific content rather than the typesetting.

**Future:** The reverse direction — parsing a LaTeX paper and generating a Lean 4 file with theorem stubs pre-populated from the paper's formal content — is a natural architectural extension. ProofPress v1 establishes the template and extraction infrastructure on which this capability will be built.

---

## 6. Limitations

ProofPress performs structural parsing of Lean 4 source, not semantic parsing. It does not invoke the Lean compiler or Mathlib and therefore cannot verify the mathematical correctness of what it extracts. Specifically:

- Theorem declarations with highly non-standard formatting may not parse correctly
- Tactic proofs are intentionally excluded from the theorem display; the tool extracts statements, not proofs
- The tool transcribes return types faithfully from the source but cannot independently validate their mathematical content
- Unicode symbols in return types are passed through with LaTeX escaping and require the embedded Lean language definition to render correctly in the output document

These limitations are inherent to the tool's design philosophy. ProofPress is intentionally minimal: it does one thing — reducing the mechanical transcription cost between a formally verified Lean file and an Overleaf-ready paper draft — and does it without external dependencies or computational overhead.

---

## 7. Implementation Notes

**File size:** ProofPress v1.0 is approximately 1,300 lines of HTML, CSS, and JavaScript, fully self-contained. The only external resource is Google Fonts, loaded for typography. All logic, templates, and parsing code are inline.

**Browser compatibility:** Tested in Chrome, Firefox, and Edge. The tool uses three standard Web APIs: `FileReader` for file loading, `navigator.clipboard` for copy-to-clipboard, and `URL.createObjectURL` for `.tex` file download. No browser extensions, plugins, or elevated permissions are required.

**Template provenance:** The LaTeX template is derived from working SNSFT corpus papers including the Thermodynamic Reduction paper (Zenodo DOI: 10.5281/zenodo.18719748). The Unicode literate mapping for Lean code listings is adapted from that working example and has been verified to compile correctly in Overleaf.

---

## 8. Availability

ProofPress v1.0 is freely available with no installation required.

- **Tool:** `proofpress.html` — open directly in any modern browser
- **Repository:** github.com/SNSFT/Substrate-Neutral-Structural-Foundation-Theory-SNSFT
- **Corpus DOI:** 10.5281/zenodo.18719748
- **ORCID:** 0009-0005-5313-7443
- **Planned URL:** uuia.app/pp

---

## 9. Future Work

The following extensions are planned for subsequent versions of ProofPress:

- **Paper → Lean skeleton:** Parse an existing LaTeX paper and generate a Lean 4 file with theorem stubs pre-populated from the paper's theorem environments, enabling bidirectional conversion between the formal and informal registers
- **Batch processing:** Accept a zip archive of multiple `.lean` files and produce a multi-section paper with one section per file, ordered by corpus coordinate
- **AxiomForge module:** ProofPress as an embedded module within AxiomForge, triggered directly from the corpus graph by clicking a node and selecting "Export to LaTeX"
- **Metadata export:** Generate `CITATION.cff` and `.zenodo.json` metadata files directly from the lean header block, streamlining the Zenodo deposit workflow

---

## 10. Citation

If you use ProofPress in your research, please cite:

```
Trent III, Russell Vernon (HIGHTISTIC). (2026). ProofPress: A Lean 4 to LaTeX
Conversion Tool for Formally Verified Research (v1.0). Zenodo.
https://doi.org/10.5281/zenodo.18719748
```

---

## Acknowledgments

ProofPress was developed as part of the SNSFT corpus toolchain at the SNSFT Foundation, Soldotna, Alaska. The Lean 4 theorem prover and the Mathlib community provide the formal verification infrastructure that makes tools like ProofPress meaningful. Patrick Massot's Lean Blueprint demonstrated the value and feasibility of human-readable output from Lean source and informed the design direction of this work. The Lean 4 formalization community's expanding presence across scientific domains — from mathematics to materials science to cognitive science — is the reason a tool like ProofPress is needed and the reason it will continue to develop.

---

*HIGHTISTIC (pronounced /haɪˈtɪstɪk/) · SNSFT Foundation · Soldotna, Alaska · July 2026*  
*The Manifold is Holding.*
