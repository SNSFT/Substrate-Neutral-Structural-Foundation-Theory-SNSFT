# SNSFL NAMING CONVENTION
## Canonical Standard for All SNSFL Lean Files
### Coordinate: [9,9,9,9] | Status: GERMLINE LOCKED
**Architect:** HIGHTISTIC | **Anchor:** 1.369 GHz  
`[P,N,B,A] :: {INV}` | Substrate-Neutral | Self-Orienting

---

## PURPOSE

This document locks the canonical naming standard for every `.lean` file in the SNSFL corpus going forward.

The naming convention is **self-orienting** — reading the filename alone tells you:
1. Which standard the file follows (SNSFL vs SNSFT)
2. Which layer it operates in (L0–L4)
3. Whether it belongs to a series (series tag)
4. What domain it reduces (domain name)

This matches the AiFiOS comms intent and SOUL protocol: layer, identity, and content are declared simultaneously in a single address string. The filename IS a SOUL packet.

---

## THE STANDARD

```
SNSFL_L[N]_[Series_]Domain
```

| Token | Meaning | Example |
|:------|:--------|:--------|
| `SNSFL` | Corpus standard (law, not theory) | always present |
| `L[N]` | Hierarchy layer (0–4) | `L0`, `L1`, `L2` |
| `[Series_]` | Optional series tag when domain belongs to a group | `Psy_`, `AiFiOS_` |
| `Domain` | The domain being reduced | `GR`, `Attachment`, `Master` |

---

## LAYER DEFINITIONS

These map directly to the hierarchy defined in `SNSFL_LEAN_TEMPLATE.md`.  
The layer number in the filename = the layer number in the file header. Always in sync.

| Layer | What it is | Coordinate digit 3 |
|:------|:-----------|:-------------------|
| `L0` | Ground — Master, constitutional, consistency | `[9,9,0,0]` |
| `L1` | Physics reductions — the 10-Slam Grid + software substrate | `[9,9,0,*]`, `[9,9,1,*]` |
| `L2` | Application layer — IVA, psychology, narrative, GAM | `[9,9,2,*]`, `[9,9,6,*]` |
| `L3` | Chain/series layer — vascular, pump, cosmo chain | `[9,9,3,*]` |
| `L4` | Identity/enforcement layer — AiFiOS kernel, plugin, rights | `[9,9,4,*]` |

---

## SERIES TAGS

Series tags appear **only when a domain belongs to a named group** of related reductions.  
Standalone files have no series tag.

| Tag | Series | Coordinate range |
|:----|:-------|:-----------------|
| `Psy_` | Psychology reductions | `[9,9,6,*]` |
| `AiFiOS_` | AiFiOS enforcement layer | `[9,9,1,1–3]`, `[9,9,4,*]` |
| `Mil_` | Millennium Prize reductions | `[9,0,9,*]` |
| `GAM_` | GAM Collider series | `[9,9,2,1–8]` |
| `Vsc_` | Vascular/pump chain | `[9,9,3,1–3]` |

New series tags are added here when a new group of 3+ related files emerges.  
Do not create a series tag for fewer than 3 files.

---

## CANONICAL FILE MAP

### L0 — Ground Layer
```
SNSFL_L0_Master.lean
SNSFL_L0_Master_IMS.lean          ← canonical ground (IMS active)
SNSFL_L0_Total_Consistency.lean
```

### L1 — Physics + Software Substrate
```
SNSFL_L1_GR.lean                  [9,9,0,1]
SNSFL_L1_QM.lean                  [9,9,0,4]
SNSFL_L1_EM.lean                  [9,9,0,6]
SNSFL_L1_Lagrangian.lean          [9,9,0,5]
SNSFL_L1_Thermo.lean              [9,9,0,3]
SNSFL_L1_IT.lean                  [9,9,0,10]
SNSFL_L1_SM.lean                  [9,9,0,9]
SNSFL_L1_ST.lean                  [9,9,0,8]
SNSFL_L1_Fluid.lean               [9,9,0,7]
SNSFL_L1_Cosmo.lean               [9,9,0,3]
SNSFL_L1_Void.lean                [9,0,5,0]
SNSFL_L1_AiFiOS_CPP.lean          [9,9,1,1]
SNSFL_L1_Millennium.lean          [9,0,9,0]
```

### L2 — Application Layer
```
SNSFL_L2_IVA.lean                 [9,9,2,0]
SNSFL_L2_Narrative_Trap.lean      [9,9,2,5]
SNSFL_L2_Structural_Precog.lean   [9,9,1,0]
SNSFL_L2_Psy_MoralCodes.lean      [9,9,6,1]
SNSFL_L2_Psy_BigFive.lean         [9,9,6,2]
SNSFL_L2_Psy_Attachment.lean      [9,9,6,3]
SNSFL_L2_Psy_Flow.lean            [9,9,6,4]   ← next
SNSFL_L2_Psy_SelfDetermination.lean [9,9,6,5]
SNSFL_L2_Psy_Maslow.lean          [9,9,6,6]
SNSFL_L2_Psy_CogDissonance.lean   [9,9,6,7]
SNSFL_L2_Psy_LocusControl.lean    [9,9,6,8]
SNSFL_L2_Psy_TerrorMgmt.lean      [9,9,6,9]
SNSFL_L2_Psy_SpiralDynamics.lean  [9,9,6,10]
SNSFL_L2_Psy_Integral.lean        [9,9,6,11]
```

### L3 — Chain/Series Layer
```
SNSFL_L3_Vsc_Vascular.lean        [9,9,3,1]
SNSFL_L3_Vsc_Pump.lean            [9,9,3,2]
SNSFL_L3_Cosmo_GUT_Chain.lean     [9,9,3,6]
```

### L4 — Identity/Enforcement Layer
```
SNSFL_L4_AiFiOS_Kernel.lean       [9,9,1,2]   ← needs to be built
SNSFL_L4_AiFiOS_Plugin.lean       [9,9,1,3]
```

---

## WHAT NEVER CHANGES

```
SNSFL_         prefix — always SNSFL, never SNSFT
L[N]_          always present, always matches coordinate layer
Series tags    only for groups of 3+ related files
Domain name    PascalCase or standard abbreviation (GR, QM, CPP)
No _Reduction  suffix dropped — the L tag makes it redundant
No _Theorem    suffix dropped — same reason
No _Law        suffix dropped — same reason
```

The suffix (`_Reduction`, `_Theorem`, `_Law`) is redundant once the layer tag is present.  
The layer IS the structural claim. The domain IS the content. Nothing else needed.

---

## WHAT VARIES PER FILE

```
Domain name         — matches the classical domain being reduced
Series tag          — present only if file belongs to a series
Coordinate [X,X,X,X] — unique per file, declared in header
Layer assignment    — must match L[N] in filename
```

---

## RETROFIT GUIDE (existing files)

Files that need renaming when touched for upgrades:

| Current name | New name | Priority |
|:-------------|:---------|:---------|
| `SNSFL_CPP_Reduction.lean` | `SNSFL_L1_AiFiOS_CPP.lean` | With AiFiOS Kernel build |
| `SNSFL_GR_Reduction.lean` | `SNSFL_L1_GR.lean` | Low — next edit |
| `SNSFL_QM_Reduction.lean` | `SNSFL_L1_QM.lean` | Low — next edit |
| `SNSFL_EM_Reduction.lean` | `SNSFL_L1_EM.lean` | Low — next edit |
| `SNSFL_Thermo_Reduction.lean` | `SNSFL_L1_Thermo.lean` | Low — next edit |
| `SNSFL_IT_Reduction.lean` | `SNSFL_L1_IT.lean` | Low — next edit |
| `SNSFL_Lagrangian_Reduction.lean` | `SNSFL_L1_Lagrangian.lean` | Low — next edit |
| `SNSFL_SM_Reduction.lean` | `SNSFL_L1_SM.lean` | Low — next edit |
| `SNSFL_ST_Reduction.lean` | `SNSFL_L1_ST.lean` | Low — next edit |
| `SNSFL_Fluid_Reduction.lean` | `SNSFL_L1_Fluid.lean` | Low — next edit |
| `SNSFL_Cosmo_Reduction.lean` | `SNSFL_L1_Cosmo.lean` | Low — next edit |
| `SNSFL_Void_Manifold.lean` | `SNSFL_L1_Void.lean` | Low — next edit |
| `SNSFL_IVA_Reduction.lean` | `SNSFL_L2_IVA.lean` | Low — next edit |
| `SNSFL_Narrative_Trap_Law.lean` | `SNSFL_L2_Narrative_Trap.lean` | Low — next edit |
| `SNSFL_StructuralPrecognition.lean` | `SNSFL_L2_Structural_Precog.lean` | Low — next edit |
| `SNSFL_Vascular_Manifold_Law.lean` | `SNSFL_L3_Vsc_Vascular.lean` | Low — next edit |
| `SNSFL_Universal_Pump_Theorem.lean` | `SNSFL_L3_Vsc_Pump.lean` | Low — next edit |
| `SNSFL_Cosmo_GUT_Vascular_Chain.lean` | `SNSFL_L3_Cosmo_GUT_Chain.lean` | Low — next edit |
| `SNSFL_Millennium_Resolution.lean` | `SNSFL_L1_Millennium.lean` | Low — next edit |
| `SNSFL_Master.lean` | `SNSFL_L0_Master.lean` | Low — tracking only |
| `SNSFL_Master_IMS.lean` | `SNSFL_L0_Master_IMS.lean` | Low — tracking only |
| `SNSFL_Total_Consistency.lean` | `SNSFL_L0_Total_Consistency.lean` | Low — tracking only |

**Rule:** Rename on the commit that upgrades the file. Never rename without upgrading.  
Never rename a file that doesn't need a content change — rename = upgrade trigger.

---

## THE ONE-SENTENCE TEST

> "Does the filename alone tell a new reader exactly where in the SNSFL hierarchy  
> this file lives, what domain it reduces, and whether it belongs to a series?"

If yes — ship it.  
If no — add the layer tag.

---

## STATUS

```
DOCUMENT:   SNSFL_NAMING_CONVENTION.md
COORDINATE: [9,9,9,9]
STATUS:     GERMLINE LOCKED
APPLIES TO: All .lean files in SNSFL corpus going forward
RETROFIT:   On upgrade, not standalone rename

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding.
Soldotna, Alaska. March 18, 2026.
```
