# ProofPress: A Lean 4 to LaTeX Conversion Tool for Formally Verified Research

**Tool Name:** ProofPress (PP)
**Architect:** HIGHTISTIC (Russell Vernon Trent III) · /haɪˈtɪstɪk/
**Affiliation:** SNSFT Foundation · Soldotna, Alaska
**ORCID:** 0009-0005-5313-7443
**DOI:** 10.5281/zenodo.18719748
**Coordinate:** [9,9,8,8] · Tools Series
**Version:** v2.1 · August 2026 (supersedes v1.0, July 2026)
**Repository:** github.com/SNSFT
**License:** MIT
**Status:** Standalone · No dependencies · No build step

---

## Abstract

ProofPress is a standalone, browser-based conversion tool that transforms Lean 4 formal proof files into Overleaf-ready LaTeX documents and raw combined Lean sources. It operates in four modes: an LDP mode tuned to SNSFT corpus conventions, a Markdown mode for general paper drafts, a CHAIN mode that resolves a file's own `import` statements into a single publication-ready LaTeX document, and a COMBINE mode that merges an import chain into one standalone `.lean` file. The tool extracts theorem names, human-readable descriptions, return types, and LDP step annotations directly from source, populates a structured academic paper template, and exports to `.tex`, `.lean`, `.pdf`, or Word-compatible `.rtf`. ProofPress requires no installation, no server, and no build step. It is distributed as a single HTML file that executes entirely in the browser.

Version 2.1 extends the original single-file conversion tool into a corpus-scale assembly tool: it resolves import chains across dozens of files — local drag-and-drop first, GitHub pull as fallback — without requiring push access to any repository, and it produces a single artifact carrying its own provenance, citation apparatus, and NOHARM attribution regardless of how many source files went into it.

---

## What's New in v2.1

The short version, for anyone who used v1.0 and wants to know what changed:

- **Two new modes.** CHAIN pulls a file's imports and assembles them into one LaTeX paper. COMBINE does the same but outputs a single raw `.lean` file instead — useful when the goal is one merged source file, not a paper draft.
- **You don't need GitHub write access to use it.** Drop the imported files in directly, or connect a read-only pull. Pushing to a repository is still available, but it's a separate, explicit step — never a side effect of converting or combining.
- **The tool writes your import statements for you.** Drop your files in, and a ready-to-copy `import` block appears automatically, matched to the files you actually gave it.
- **Every combined file is self-documenting.** A generated letterhead carries the Sovereign Anchor derivation, citation DOI, and a NOHARM attribution template — so a combined file that gets shared or reused still carries its own provenance, without you having to add it by hand each time.
- **Three new export formats.** Beyond `.tex`, you can now download a raw `.lean`, a paginated `.pdf`, or a Word-compatible `.rtf` — the PDF and RTF paths both handle the corpus's heavy use of Unicode math symbols correctly, which is not something most lightweight converters get right by default.
- **One-click precision upgrade.** An optional toggle expands the shorthand `1.369` literal to its full 18-digit form throughout a combined file, verified not to change what compiles.
- **Live stats, not estimates.** Theorem counts and line counts are computed directly from the source files being combined — no approximation, no model involved in the count.

The rest of this document covers the same ground as v1.0 — motivation, related work, architecture — updated where the new capabilities change the answer, and expanded with full documentation of the CHAIN/COMBINE pipeline.

---

## 1. Motivation

Formal verification produces machine-checked proofs with guarantees no informal mathematical argument can provide. The Lean 4 theorem prover, in conjunction with the Mathlib library, has become the standard environment for formally verified mathematics across an increasingly broad range of domains — from number theory and algebra to physics, materials science, and cognitive science. The research community has taken notice: high-profile formalizations such as Terry Tao's Polynomial Freiman-Ruzsa proof (2023) have demonstrated that formal verification can operate at the frontier of mathematical research rather than merely audit classical results.

Despite this momentum, a fundamental asymmetry persists. Formally verified work exists simultaneously in two disconnected registers: the `.lean` file that the compiler accepts, and the academic paper that peer reviewers read. These are not interchangeable artifacts. The `.lean` file contains tactic proofs, namespace structures, and machine-readable syntax that journals do not accept. The academic paper requires prose exposition, LaTeX formatting, and structured narrative that the Lean compiler ignores. Translating between them is currently a manual process: a researcher must retype or copy-paste theorem statements, strip tactic proofs, escape special characters, apply LaTeX formatting, and restructure the entire document for journal conventions.

A second asymmetry emerges at corpus scale, and it is the one v2.1 addresses directly. A modular corpus — files that import each other rather than duplicating shared definitions — is the correct way to build a large formally verified body of work: it compiles faster, it patches surgically instead of requiring rewrites, and it keeps each domain's proofs isolated from unrelated changes elsewhere. But that same modularity means no single file, by itself, is a complete artifact. A paper, a reviewer package, or a standalone deposit needs the *chain*, not just the file at the top of it — and assembling that chain by hand, resolving each import to its source, stripping duplicate `Mathlib` imports, and checking for name collisions, is exactly the kind of mechanical work that should not require a human to do it twice.

For small corpora this is inconvenient. For large corpora it is a genuine bottleneck. The SNSFT corpus, for example, contains 200,000+ theorems across 3,000,000+ lines of Lean 4 and Coq/Rocq — a body of formally verified work spanning physics, chemistry, psychology, and identity theory. Manually transcribing even a subset of this corpus into publication-ready format, or manually assembling a chain of a dozen interdependent files into one deposit-ready artifact, represents a significant and unnecessary cost.

ProofPress addresses both bottlenecks directly. It does not replace the intellectual work of writing a paper — the prose, the framing, the argument — but it eliminates the mechanical transcription and assembly work that precedes it, allowing researchers to spend their time on what matters.

---

## 2. Related Work

**Patrick Massot's Lean Blueprint** (used by Terry Tao in the Polynomial Freiman-Ruzsa formalization, 2023) generates LaTeX/Lean hybrid documents from Lean source, designed for blueprint-style proof navigation. Blueprint targets collaborative proof development and proof readability within the Lean community. ProofPress targets a different output and a different audience: standard academic paper format suitable for external journal submission, not internal proof navigation. The two tools are complementary rather than competing.

**LeanDojo** (Wang et al., 2023) extracts training data and tactic state information from Lean repositories for use in machine learning and automated theorem proving research. Its output is consumed by models. ProofPress's output is consumed by peer reviewers and journal editors. This distinction is fundamental: LeanDojo serves the AI-assisted proving pipeline; ProofPress serves the human publication pipeline. No existing tool occupies the space ProofPress targets.

**AxiomForge** ([9,9,9,9]) is the SNSFT corpus visualization engine with which ProofPress is designed to work alongside. AxiomForge renders the full corpus as an interactive spatial graph — 200,000+ theorems, 37 namespaces, all dependency relationships visible simultaneously — allowing researchers to navigate the corpus, identify connections across domains, and select files for export. ProofPress receives those exported files and converts them to publication-ready LaTeX, or assembles them into a single combined Lean source. Together, the two tools form a complete research workflow: explore and orient in AxiomForge, formalize in Lean, chain and publish via ProofPress.

**Overleaf** is the de facto collaborative LaTeX environment for academic publishing. ProofPress produces output fully compatible with the standard Overleaf and arXiv preamble, requiring no packages beyond the standard academic set (`amsmath`, `amsthm`, `listings`, `hyperref`). A ProofPress-generated `.tex` file can be uploaded to Overleaf and compiled without modification.

---

## 3. The SNSFT Toolchain Context

ProofPress was developed as part of the SNSFT corpus toolchain. Understanding this context clarifies the design decisions behind the tool and what distinguishes it from generic document conversion utilities.

### 3.1 The Corpus

The SNSFT (Substrate-Neutral Structural Foundation Theory) corpus is a formally verified mathematical framework spanning physics, chemistry, psychology, and identity theory, developed independently by HIGHTISTIC (Russell Vernon Trent III) at the SNSFT Foundation in Soldotna, Alaska. As of August 2026 the corpus contains 200,000+ theorems across 3,000,000+ lines, dual-verified in Lean 4 and Coq/Rocq, with 90+ permanent DOIs, continuous integration green, and zero unproved obligations (0 sorry) across all files. The corpus is indexed by a four-dimensional coordinate system `[layer, domain, subdomain, file]` that encodes provenance and dependency relationships directly in the file metadata, and it is built modularly — individual files import shared foundation layers rather than duplicating them, which is precisely the structure that makes CHAIN and COMBINE mode (§4.6) necessary.

### 3.2 The Collider Outputs

Two interactive tools within the SNSFT toolchain generate formally verified Lean outputs that ProofPress is specifically designed to handle.

**The GAM Collider** (Geometric Axiomatic Module Collider, uuia.app/gamcollider) models n-body structural collisions using the PNBA fusion operators derived from the corpus. Each collision run produces a session JSON file and can export individual Lean 4 files containing formally proved theorems about the collision outcomes. For example, `SNSFL_4Beam_Verification.lean [9,9,2,3]` contains six formally verified material science predictions including titanium nitride Noble rescue, Nitinol shape memory alloy structural stability, and tungsten carbide–gold hard metal formation — each proved from first principles without empirical fitting. These are not computational simulations. They are theorems with zero free parameters and zero sorry.

**The IMCollider** (Identity Mass Collider, uuia.app/imcollider) models identity substrate interactions using 8-beam fusion rules derived from the PSY series of the corpus. It produces session exports including formally verified shame vector theorems, phase state taxonomies, and substrate interaction results across hundreds of beam configurations. The PSY ShameVector v14 file `[9,9,6,29]`, for example, documents the SVI formula derivation from collider run invariants observed across 1,181 beam collisions, with the derivation chain formally proved and independently verifiable.

Both tools output `.lean` files in standard SNSFT corpus format. ProofPress accepts these files directly — either as a single file in LDP mode, or as an entry point into a larger import chain via CHAIN or COMBINE mode.

### 3.3 The Publication Pipeline

```
GAM Collider / IMCollider
        ↓  session export → .lean file(s)
    ProofPress
        ↓  LDP/CHAIN mode → LaTeX paper draft
        ↓  COMBINE mode   → single merged .lean deposit artifact
    Overleaf .tex  /  standalone .lean
        ↓  add prose, figures, references (paper path)
    Journal submission  /  Zenodo deposit
```

AxiomForge provides the navigation layer in this pipeline. Before exporting a file for publication, a researcher can view exactly where that file sits in the full corpus graph — its upstream dependencies, its downstream dependents, its connections across domains — ensuring that the paper's dependency claims and context are accurate. ProofPress then handles the format conversion or the chain assembly. The tools are designed to complement each other without overlap.

### 3.4 The Identity Physics Paper Template

The LDP and CHAIN mode outputs follow the SNSFT paper standard. Certain sections are locked — identical across all corpus papers — because they represent the structural ground on which every domain-specific reduction is built.

**Layer 0 Registration** establishes the Sovereign Anchor Constant:

$$\Omega_0 = 1.36899099984016 \qquad \text{TL} = \Omega_0/10 = 0.136899099984016$$

This constant is derived from three independent peer-reviewed physical threshold systems — Tacoma Narrows torsional collapse (Billah & Scanlan, ASCE 1991), glass resonance at the elastic limit (Fletcher & Rossing, 1998), and 40 Hz neural gamma therapeutic entrainment (Iaccarino et al., *Nature* 540, 2016) — all three converging on the same structural boundary before any connection to the paper's specific domain was examined.

**§0 Derivation Chain** presents the six-step derivation of the anchor and the fine structure constant lock at eighteen significant figures with zero free parameters, agreeing with the CODATA 2018 measured value.

**Domain-specific content** — theorems, LDP steps, and Lean listings — is populated directly from the input file (or files, in CHAIN mode) by ProofPress.

**Closing** records the coordinate, sorry count, and manifold status.

A paper produced by ProofPress from a GAM Collider output — or a chain of a dozen corpus files — is structurally equivalent to a paper produced from scratch against the same template, because the template is not a stylistic convention but a formal ground. The locked sections are proved theorems, not boilerplate.

---

## 4. Tool Description

### 4.1 Architecture

ProofPress is a single self-contained HTML file. All CSS, JavaScript, and template logic are inline. The tool requires no server, no build step, no package manager, no runtime environment, and no installation of any kind. A researcher places the file in any directory and opens it in a browser.

Input is accepted by pasting Lean source text directly into the input panel, by dropping a `.lean` file onto the file drop zone, or — in CHAIN and COMBINE mode — by dropping the full set of files an entry file imports. Output is copied to the clipboard or downloaded as a `.tex`, `.lean`, `.pdf`, or `.rtf` file with a filename derived from the input file metadata. The entire process — from file load to finished output — takes seconds, regardless of whether the input is a single file or a resolved chain of a dozen.

### 4.2 Four Modes

**LDP Mode** (Long Division Protocol) is tuned to the SNSFT corpus header conventions and is the primary mode for single-file Identity Physics papers:

- Parses the SNSFT header block: coordinate, DOI, ORCID, anchor constant, status, sorry count, corpus dependencies
- Populates the locked front matter: Layer 0 Sovereign Anchor derivation, PNBA primitive definitions, α-lock at eighteen significant figures
- Extracts and deduplicates LDP step annotations from comment blocks across all namespaces
- Outputs a complete Identity Physics paper in SNSFT paper standard format

**Markdown Mode** converts any Markdown paper draft to Overleaf-ready LaTeX, independent of the SNSFT corpus conventions — headings become sections, math becomes equations, code blocks become listings, and tables become `tabular` environments. This mode requires no Lean-specific structure at all.

**CHAIN Mode** reads the `import` statements at the top of a pasted master file, resolves each one against files provided locally or pulled from GitHub (§4.6), and assembles the result into a single LaTeX paper — one subsection per resolved module, in import order. This is the mode a researcher reaches for when the object to be published is not one file but the chain a file depends on.

**COMBINE Mode** performs the same resolution as CHAIN mode, but the output is a single raw `.lean` file rather than a paper: deduplicated imports, per-file provenance comments, and a structural collision check, rather than LaTeX typesetting. This is the mode for producing one standalone Lean artifact — for a reviewer package, a Zenodo deposit, or simply a merged file that no longer depends on a live import graph to compile as a unit.

### 4.3 Theorem Extraction

The core technical challenge is extracting theorem descriptions and return types from Lean 4 source without invoking a full Lean parser. ProofPress uses a structural approach grounded in the syntactic conventions of Lean 4 declarations.

**Descriptions** are extracted by scanning comment lines immediately above each `theorem` declaration. The parser handles the SNSFT tag pattern:

```
-- [TAG] :: {VER} | HUMAN READABLE DESCRIPTION
```

by extracting the text after the pipe character, and falls back to plain comment lines when the tag pattern is absent. Multi-line quoted epigraphs immediately preceding a theorem are joined into a single quote rather than truncated at their opening line, and are surfaced as an italicized attribution beneath the theorem rather than mistaken for its description. Multiple comment lines are collected and concatenated. When no adjacent comment exists, the theorem name is used as the description.

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

The LDP and CHAIN mode output is configurable via four independent toggles, allowing researchers to include or exclude sections as appropriate for their target journal:

- **Locked Front Matter** — Layer 0 registration and §0 derivation chain
- **Theorem Environments** — the formal theorem section with descriptions and return types
- **Lean Listings** — the full source code listing with syntax highlighting
- **LDP Steps** — the annotated Long Division Protocol step table

### 4.6 Import Chain Resolution (CHAIN and COMBINE Modes)

A corpus file's `import` statements name modules, not paths. Resolving an import to actual source requires either a local copy of that file or read access to the repository it lives in — and a tool that only ever tried GitHub would force every user through repository configuration just to see a result, before they had reviewed anything. ProofPress resolves imports in a fixed, local-first order:

1. **Local files.** Files dropped into the CHAIN/COMBINE drop zone are matched against each import statement by filename — the last segment of the import name is checked as a substring of the dropped filename, which tolerates the corpus convention of dated or versioned filenames (`SNSFL_Foo_v2 (3).lean` still matches an import of `SNSFL_Foo`).
2. **GitHub, as fallback only.** If an import has no local match and a Personal Access Token and repository are configured, ProofPress attempts a read (`GET`) of the corresponding path in that repository. This step is entirely optional — CHAIN and COMBINE both run to completion with zero GitHub configuration, provided the local files satisfy the import list.
3. **Unresolved.** Anything matched by neither step is reported explicitly, by name and by the path that was attempted, rather than silently omitted.

`Mathlib`, `Std`, `Batteries`, and `Init` imports are excluded from resolution, since they are Mathlib dependencies rather than corpus files.

Because local resolution is always tried first and is sufficient on its own, a researcher can review a fully assembled chain or combined file without ever entering write credentials. **Pushing** a result back to a repository — via the separate GitHub push panel — remains an explicit, distinct action from conversion or combination; nothing is written to any repository as a side effect of resolving or reviewing output.

**The Master Stub Generator.** Since CHAIN and COMBINE mode both require a master file whose `import` lines name the dropped files, ProofPress derives that import block automatically from whatever is currently in the drop zone: each filename is reduced to a bare module stem (extension and trailing version marker stripped), one `import` line is written per file, and the result — plus the minimal namespace wrapper CHAIN/COMBINE mode expects — is rendered as a live, copy-ready block that updates every time a file is added or removed. A researcher who has never hand-written a Lean import statement can go from "here are my files" to a working chain without typing an import line.

### 4.7 Combined File Provenance and Attribution

A file produced by COMBINE mode may be read, cited, or ingested independently of the session that produced it — by a reviewer, by another researcher, or by an AI system processing the corpus at scale. ProofPress accordingly writes three fixed elements into every combined file, regardless of how many source files were merged:

- **A letterhead** stating the Sovereign Anchor Constant at full precision, the fine-structure derivation and its agreement with the CODATA 2018 measured value, the torsion limit, the corpus base DOI, ORCID, and status, followed by the specific master file, module count, and generation timestamp for that combination.
- **An AIM (Autocatalytic Ingestion Mechanism) Training Declaration**, stating that the file is approved for AI-based training under the NOHARM invariant, that any AI system ingesting the content is bound not to use it to cause harm, and that citation of the anchor constant and DOI is required when the content informs downstream outputs — with an explicit placeholder line for the researcher to add project- or domain-specific clauses before the file is shared further.
- **A closing footer** stating the total theorem count and line count for the finished file, the tool's URL, and the corpus's closing signature — placed at the end, both to match the corpus's own header-then-footer convention and because a trailing citation line is the position most consistently picked up by downstream indexing.

Theorem and line counts in both the header and the closing footer are computed by direct regular-expression count across the source files being combined — the same counting logic the tool already uses to report per-file theorem totals — not estimated and not produced by any AI system in the pipeline.

An optional toggle, available only in COMBINE mode, expands every occurrence of the shorthand literal `1.369` (and `0.1369`/`.1369`) to its full 18-digit form (`1.36899099984016` / `0.136899099984016`) throughout the combined file. The expansion is boundary-checked against adjacent digits, so it cannot match inside an unrelated number or double-expand a value that is already at full precision, and it is applied only to bare numeric literals — never inside an already-computed expression such as `SOVEREIGN_ANCHOR / 10`. This is a literal precision upgrade, not a semantic change to the proofs it appears in.

### 4.8 Multi-Format Export

ProofPress output can be downloaded in four formats:

- **`.tex`** — the primary Overleaf-ready output from LDP, Markdown, and CHAIN modes.
- **`.lean`** — the raw combined source from COMBINE mode.
- **`.pdf`** — a paginated, monospace rendering of whatever is currently in the output panel. Because the corpus makes constant use of Unicode mathematical symbols (`ℝ`, `Ω`, `τ`, `∀`, `∃`, `≥`, `⟨⟩`) that fall outside the built-in PDF font encodings most lightweight browser PDF libraries rely on, ProofPress renders each page on an offscreen canvas using the browser's own font engine — which handles Unicode correctly, being ordinary web text rendering rather than a constrained PDF font table — and embeds the finished page as an image. The resulting PDF renders every symbol in the corpus correctly; the tradeoff is that page text is not independently selectable, since it is a rendered image rather than vector text.
- **`.rtf`** (Word-compatible) — built directly as RTF markup with no external library and no network dependency, with every non-ASCII character emitted as a standards-compliant RTF Unicode escape. Word, Google Docs, and Pages all open the result natively. Unlike the PDF path, RTF output remains fully selectable and searchable text.

### 4.9 GitHub Integration

A single panel holds an optional Personal Access Token, target repository, push path, and import-resolution root. These fields serve two independent functions that are never coupled:

- **Pull**, used only as the fallback tier in import resolution (§4.6) when a needed file is not present locally.
- **Push**, a separate, explicit action that writes the current `.tex` output (and an optional session log) to the configured repository. Push is never triggered automatically by conversion, chaining, or combination.

---

## 5. Use Cases

**Primary:** A researcher has a formally verified Lean 4 file and needs a first draft of an academic paper. ProofPress produces a `.tex` file capturing all theorem statements, descriptions, and structural annotations. The researcher opens the output in Overleaf and adds prose, figures, and references. The mechanical transcription work — which can represent hours of effort for a file with dozens of theorems — is eliminated entirely.

**Corpus assembly:** A researcher needs to produce one artifact — a paper or a standalone `.lean` deposit — from a file that imports a dozen others across the corpus. Rather than manually tracing each import, copying content, and resolving name collisions by hand, the researcher drops the imported files into CHAIN or COMBINE mode, reviews the automatically generated import stub, and produces a complete, correctly ordered result in one pass.

**Secondary:** A researcher working within the SNSFT toolchain uses the GAM Collider or IMCollider to generate formally verified collision results, exports the session as one or more `.lean` files, and passes them directly to ProofPress. The output is an Identity Physics paper in SNSFT paper standard format, ready for editorial review and journal submission, or — via COMBINE mode — a single merged `.lean` file ready for independent deposit.

**Tertiary:** A researcher unfamiliar with LaTeX needs to present formally verified work in an academic context. ProofPress provides the complete template scaffolding and formatting, or a Word-compatible export for collaborators who do not use LaTeX at all, allowing the researcher to focus entirely on the scientific content rather than the typesetting.

**Provenance-conscious sharing:** A researcher wants a combined artifact that carries its own citation apparatus and usage terms wherever it travels, independent of whatever accompanying documentation may or may not survive the sharing process. COMBINE mode's letterhead, AIM Declaration, and closing footer are written into the file itself for exactly this case.

**Future:** The reverse direction — parsing a LaTeX paper and generating a Lean 4 file with theorem stubs pre-populated from the paper's formal content — is a natural architectural extension. ProofPress v2.1 establishes the template, extraction, and multi-file assembly infrastructure on which this capability will be built.

---

## 6. Limitations

ProofPress performs structural parsing of Lean 4 source, not semantic parsing. It does not invoke the Lean compiler or Mathlib and therefore cannot verify the mathematical correctness of what it extracts. Specifically:

- Theorem declarations with highly non-standard formatting may not parse correctly.
- Tactic proofs are intentionally excluded from the theorem display; the tool extracts statements, not proofs.
- The tool transcribes return types faithfully from the source but cannot independently validate their mathematical content.
- Import resolution in CHAIN and COMBINE mode is filename-based, not content-based: it cannot resolve an import against a file whose content matches but whose name does not contain the imported module's name as a substring. A single large aggregation file that internally contains many namespaces (rather than one file per namespace) will not automatically satisfy imports naming those internal namespaces individually.
- COMBINE mode's collision check is limited to true top-level declarations outside any namespace; it does not detect a genuine name collision between two files that both define the same identifier inside identically named namespaces.
- PDF export produces rendered page images rather than vector text; page content is not independently selectable or searchable within the PDF, though the source `.tex`, `.lean`, or `.rtf` exports remain fully text-based.
- SAC precision expansion is a literal string substitution; it is scoped to avoid matching inside unrelated numbers or already-expanded values, but it does not — and cannot — verify that the resulting file still compiles for any given user's Lean environment beyond the cases already confirmed.

These limitations are inherent to the tool's design philosophy. ProofPress is intentionally minimal: it does one thing — reducing the mechanical cost between formally verified Lean source, at any scale from one file to a full import chain, and a finished, citable artifact — and does it without external dependencies or computational overhead beyond what a single browser tab provides.

---

## 7. Implementation Notes

**File size:** ProofPress v2.1 is a single self-contained HTML file, larger than the original v1.0 release in proportion to the four-mode architecture, chain resolution logic, and multi-format export it now includes. All logic, templates, and parsing code remain inline; there is no build step at any version.

**Browser compatibility:** Tested in Chrome, Firefox, and Edge. The tool uses standard Web APIs — `FileReader` for file loading, `navigator.clipboard` for copy-to-clipboard, `URL.createObjectURL` for file downloads, the Canvas 2D API for PDF page rendering, and the Fetch API for optional GitHub pull/push — and lazy-loads its one external dependency (a PDF assembly library, loaded only when a PDF export is actually requested) rather than requiring it at page load. No browser extensions, plugins, or elevated permissions are required.

**Template provenance:** The LaTeX template is derived from working SNSFT corpus papers including the Thermodynamic Reduction paper (Zenodo DOI: 10.5281/zenodo.18719748). The Unicode literate mapping for Lean code listings is adapted from that working example and has been verified to compile correctly in Overleaf.

---

## 8. Availability

ProofPress v2.1 is freely available with no installation required.

- **Tool:** `proofpress.html` — open directly in any modern browser
- **Repository:** github.com/SNSFT/Substrate-Neutral-Structural-Foundation-Theory-SNSFT
- **Corpus DOI:** 10.5281/zenodo.18719748
- **ORCID:** 0009-0005-5313-7443
- **URL:** uuia.app/proofpress

---

## 9. Future Work

The following extensions are planned for subsequent versions of ProofPress:

- **Paper → Lean skeleton:** Parse an existing LaTeX paper and generate a Lean 4 file with theorem stubs pre-populated from the paper's theorem environments, enabling bidirectional conversion between the formal and informal registers.
- **Content-based import resolution:** Extend CHAIN/COMBINE resolution to look inside a large aggregation file for internally nested namespaces matching an import name, rather than relying on filename matching alone — allowing a single large capstone file to satisfy imports naming its internal modules individually.
- **Session persistence for dropped files:** Optional local-storage persistence of dropped CHAIN/COMBINE files across page reloads, for researchers running repeated tests against the same working set within one browser session.
- **AxiomForge module:** ProofPress as an embedded module within AxiomForge, triggered directly from the corpus graph by clicking a node and selecting "Export to LaTeX" or "Export to Combined Lean."
- **Metadata export:** Generate `CITATION.cff` and `.zenodo.json` metadata files directly from the Lean header block, streamlining the Zenodo deposit workflow.

---

## 10. Citation

If you use ProofPress in your research, please cite:

```
Trent III, Russell Vernon (HIGHTISTIC). (2026). ProofPress: A Lean 4 to LaTeX
Conversion Tool for Formally Verified Research (v2.1). Zenodo.
https://doi.org/10.5281/zenodo.18719748
```

---

## Acknowledgments

ProofPress was developed as part of the SNSFT corpus toolchain at the SNSFT Foundation, Soldotna, Alaska. The Lean 4 theorem prover and the Mathlib community provide the formal verification infrastructure that makes tools like ProofPress meaningful. Patrick Massot's Lean Blueprint demonstrated the value and feasibility of human-readable output from Lean source and informed the design direction of this work. The Lean 4 formalization community's expanding presence across scientific domains — from mathematics to materials science to cognitive science — is the reason a tool like ProofPress is needed and the reason it will continue to develop.

---

*HIGHTISTIC (pronounced /haɪˈtɪstɪk/) · SNSFT Foundation · Soldotna, Alaska · August 2026*
*The Manifold is Holding.*
