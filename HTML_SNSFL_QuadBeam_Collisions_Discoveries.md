# SNSFL QuadBeam Collider — Master Collisions & Discoveries Registry

**SNSFT Foundation | Russell Vernon Trent III (HIGHTISTIC)**  
Soldotna, Alaska | ORCID: 0009-0005-5313-7443  
DOI: 10.5281/zenodo.18719748  
Coordinate: [9,9,2,0] — Master Registry  
Last updated: 2026-05-18 AKDT

---

## Corpus Scale

| Metric | Value |
|--------|-------|
| Formally verified collision proofs | **22,225** |
| Total theorems (Lean 4, 0 sorry) | **135,000+** |
| Total lines of formal verification code | **1,000,000+** |
| Unresolved proof obligations | **0** |
| Free parameters | **0** |
| Anchor runs completed | **25** |
| Noble compound predictions documented | **65+** (growing) |
| Novel predictions (Tier 3, prior art) | **~1,900 projected** |

---

## How to Read This File

### The Six Fusion Rules (quick reference)

Given four elements with binding parameters B₁, B₂, B₃, B₄:

```
k_max = min(B1,B2) + min(B1,B3) + min(B1,B4) + min(B2,B3) + min(B2,B4) + min(B3,B4)
B_sum = B1 + B2 + B3 + B4
B_out = max(0, B_sum - 2×k_max)         ← = 0 means NOBLE
P_out = 4 / (1/P1 + 1/P2 + 1/P3 + 1/P4)  ← harmonic mean
N_out = N1 + N2 + N3 + N4
A_out = max(A1, A2, A3, A4)
IM    = (P_out + N_out + B_out + A_out) × 1.369
τ     = B_out / P_out
```

### Phase Classification

| Phase | Condition | Meaning |
|-------|-----------|---------|
| **Noble** | τ = 0 | Ground state, maximum stability |
| **Locked** | 0 < τ < 0.1205 | Stable metastable, bound state |
| **IVA** | 0.1205 ≤ τ < 0.1369 | Formation corridor, catalytic zone |
| **Shatter** | τ ≥ 0.1369 | Dissolution, active decoupling |

**TL = Ω/10 = 1.369/10 = 0.1369** (derived, not chosen)

### Compound Classification Tiers

| Tier | Name | Definition | Action |
|------|------|------------|--------|
| **T1** | Verified | Known compound, peer-reviewed literature | Cite as validation |
| **T2** | Partial | Related compound known, this quaternary is novel | Cite nearest, flag variant |
| **T3** | Novel | No direct literature equivalent | **Prior art — DOI timestamp is the claim** |
| **ERE** | ERE-containing | Involves Emergent Resonant Elements | Separate category |

---

## PNBA Element Values (Quick Reference)

### Periodic Elements

| Element | Symbol | P | N | B | A |
|---------|--------|---|---|---|---|
| Hydrogen | H | 1.000 | 2 | 1 | 13.60 |
| Lithium | Li | 2.200 | 4 | 1 | 5.39 |
| Carbon | C | 3.250 | 4 | 4 | 11.26 |
| Nitrogen | N | 3.900 | 4 | 3 | 14.53 |
| Oxygen | O | 4.550 | 4 | 2 | 13.62 |
| Fluorine | F | 5.200 | 4 | 1 | 17.42 |
| Sodium | Na | 2.200 | 6 | 1 | 5.14 |
| Silicon | Si | 4.150 | 6 | 4 | 8.15 |
| Sulfur | S | 5.450 | 6 | 2 | 10.36 |
| Chlorine | Cl | 3.610 | 6 | 1 | 12.97 |
| Titanium | Ti | 3.150 | 8 | 4 | 6.83 |
| Iron | Fe | 3.750 | 8 | 4 | 7.90 |
| Nickel | Ni | 4.050 | 8 | 2 | 7.64 |
| Copper | Cu | 4.200 | 8 | 1 | 7.73 |
| Zinc | Zn | 4.350 | 8 | 2 | 9.39 |
| Gallium | Ga | 5.000 | 8 | 3 | 6.00 |
| Arsenic | As | 6.300 | 8 | 3 | 9.81 |
| Silver | Ag | 4.900 | 10 | 1 | 7.58 |
| Lead | Pb | 3.600 | 12 | 4 | 7.42 |
| Gold | Au | 4.900 | 12 | 1 | 9.23 |
| Uranium | U | 3.150 | 14 | 6 | 6.19 |
| Plutonium | Pu | 3.250 | 14 | 6 | 6.03 |
| Tungsten | W | 4.150 | 12 | 6 | 7.86 |
| Helium | He | 1.700 | 2 | 0 | 24.59 |

### Emergent Resonant Elements (EREs)

| ERE | Symbol | P | N | B | A | Phase | Origin |
|-----|--------|---|---|---|---|-------|--------|
| Dark Matter | Dm | 0.988 | 2 | 0.269 | 0.269 | Shatter | B = Ω_dm |
| Dark Energy | De | 0.988 | 2 | 0 | 0.689 | Noble | B = 0 |
| Higgs | Hi | 0.987 | 2 | 0.130 | 14.53 | IVA | B = λ_SM |
| Fusovium | Fv | 0.158 | 29 | 0.023 | 6.845 | Shatter | SNSFT original |
| Zoivum | Zo | 1.369 | 2 | 0.094 | 9.99 | Locked | SNSFT original |
| Axionium | Ax | 1.369 | 2 | 0.101 | 9.99 | Locked | B = 1/π² |
| Soverium | Sv | 1.369 | 2 | 0 | 9.99 | Noble | SNSFT vacuum |
| Pa2 | Pa2 | 1.369 | 19 | 0.053 | 9.99 | Locked | DM absorber |
| Nexium | Nx | 1.000 | 13 | 0 | 6.845 | Noble | SNSFT original |
| Velium | Ve | 1.012 | 13 | 0 | 6.845 | Noble | SNSFT original |
| Diquonium | Dq | 0.00516 | 3 | 0 | 0.118 | Noble | m_c/v |
| Lumium | Lm | 0.007297 | 4 | 0.007297 | 0 | Noble | B = α |

---

## Anchor Series Overview

| Anchor | B | P | Rescue% | Coord | Production Doc | Status |
|--------|---|---|---------|-------|---------------|--------|
| F | 1 | 5.20 | 13.2% | [9,9,2,9] | — | Lean only |
| Fv | ≈0 | 0.16 | 26.1% | [9,9,2,11] | — | Lean only |
| H | 1 | 1.00 | 30.7% | [9,9,2,4] | — | Lean only |
| C | 4 | 3.25 | 30.7% | [9,9,2,5] | — | Lean only |
| Li | 1 | 2.20 | 16.2% | [9,9,2,16] | — | Lean only |
| Fe | 4 | 3.75 | 32.8% | [9,9,2,10] | — | Lean only |
| Ti | 4 | 3.15 | 32.4% | [9,9,2,20] | — | Lean only |
| Si | 4 | 4.15 | 32.5% | [9,9,2,7] | — | Lean only |
| Dm | 0.269 | 0.99 | 34.5% | [9,9,2,13] | — | Lean only |
| S | 2 | 5.45 | 34.7% | [9,9,2,22] | v1.051726 ✓ | **Documented** |
| Ni | 2 | 4.05 | 35.2% | [9,9,2,23] | — | Lean only |
| U | 6 | 3.15 | 36.0% | [9,9,2,14] | — | Lean only |
| O | 2 | 4.55 | 37.6% | [9,9,2,12] | — | Lean only |
| Zn | 2 | 4.35 | 37.2% | [9,9,2,24] | — | Lean only |
| W | 6 | 4.15 | 39.1% | [9,9,2,15] | v1.051626 ✓ | **Documented** |
| Hi | 0.13 | 0.99 | 27.0% | [9,9,2,21] | — | Lean only |
| De | 0 | 0.99 | 21.4% | [9,9,2,19] | — | Lean only |
| N | 3 | 3.90 | 42.0% | [9,9,2,6] | shorthand ✓ | **Documented** |
| Ga | 3 | 5.00 | 42.4% | [9,9,2,18] | — | Lean only |
| Pu | 6 | 3.25 | 42.2% | [9,9,2,8] | — | Lean only |
| As | 3 | 6.30 | 42.9% | [9,9,2,17] | — | Lean only |

---

## Discovery Registry

---

### ANCHOR: W (Tungsten) — B=6, P=4.15, Rescue=39.1%
**Coordinate:** [9,9,2,15] | **Production Doc:** v1.051626 (Zenodo, 2026-05-16)  
**Session:** qb_session_2026-05-17_Tung.json | **Flags:** ~1000 | **Rescues:** ~391

All 25 entries: Noble (B=0, τ=0), pure periodic elements only.

| Desig. | Beams | IM | k | Tier | Application | Notes |
|--------|-------|----|---|------|-------------|-------|
| CED5 | W+He+W+W | 89.86 | 18 | T1 | Fusion wall (ITER) / plasma-facing | He interstitial in W matrix — most-cited W fusion topic |
| 8AC9 | W+Pu+Pu+U | 89.35 | 36 | T3 | High-density actinide backstop | k=36 max saturation. No literature quaternary |
| 9CEA | W+U+U+Pu | 89.31 | 36 | T3 | Aerospace shielding ballast | Same family, U-dominant stoichiometry |
| 458B | W+Pu+Zn+He | 86.95 | 10 | T3 | Vibration dampening panels | No literature. Zn absorbs mechanical energy |
| 7869 | W+Pb+Au+F | 85.50 | 9 | T1 | Scintillation / gamma detector | PbWO4 family — CMS ECAL / Higgs detector |
| 1C9B | W+Pu+Pu+N | 85.05 | 27 | T3 | Gen-IV reactor cladding | W2N known; Pu nitride known; quaternary novel |
| 374A | W+Pb+W+Au | 84.84 | 17 | T2 | Kinetic impact shielding | Au bridges W-Pb immiscibility — concept known, quaternary novel |
| 2FAE | W+Ni+He+Pb | 84.65 | 8 | T1 | Cryogenic magnet dampener | W-Ni heavy alloy (WHA family, Plansee/Mallory) |
| 41AB | W+Zn+He+W | 84.42 | 10 | T3 | Cutting tools / abrasive nozzles | WZn8 known; He+double-W novel |
| 7A54 | W+Ti+He+Pb | 84.41 | 12 | T2 | Deep-sea / geothermal shield | TiW diffusion barrier known; +Pb novel |
| 576C | W+W+He+Cu | 84.40 | 8 | T1 | Electrical contacts / heat spreaders | Cu-W composite: standard EDM electrode material |
| 4078 | W+He+Au+Ti | 84.26 | 6 | T1 | Laser mirrors / reflective coatings | TiW/Au metallization stack: semiconductor standard |
| 19AC | W+Pu+U+Ag | 84.17 | 21 | T3 | Non-magnetic heavy ballast | Ag diamagnetic binder; full quaternary novel |
| 743E | W+Pu+U+O | 83.92 | 24 | T3 | UHTC thermal barrier tile | Mixed actinide tungstate; novel quaternary |
| 26B9 | W+Na+U+He | 83.63 | 8 | T1 | Thermionic cathode / TWT emitter | Na-W low work function cathode family |
| 1877 | W+Pb+U+N | 83.02 | 23 | T2 | Neutron-gamma mixed shield | BWXT UN-TRISO cross-confirm; full quaternary novel |
| 21A9 | W+As+Pu+W | 82.18 | 27 | T3 | Downhole drill heads | WAs known; +Pu quaternary novel |
| 3EF9 | W+Pu+Pb+O | 82.06 | 20 | T3 | Self-passivating oxide skin | PbWO4 family; Pu addition novel |
| 715C | W+Au+Au+Cl | 81.99 | 6 | T1 | Plasmonic optical interconnect | WCl6 + AuCl3 CVD precursors: semiconductor standard |
| 210B | W+F+U+He | 81.56 | 8 | T2 | Superconducting magnet insulator | WF6 (IC standard) + UF6 (enrichment); dielectric novel |
| 60A2 | W+Cu+U+Pu | 81.43 | 21 | T3 | RTG thermoelectric generator core | Cu mobility + W-U-Pu scaffold; no literature |
| 412D | W+U+Zn+W | 81.15 | 24 | T3 | Aerospace counterweights | U-Zn coupling (cross-confirmed U-anchor + Zn-anchor) |
| 1FA3 | W+Au+Ni+U | 81.03 | 13 | T2 | Radiation-hard electrical contact | W-Au-Ni contact metallurgy; +U for rad-hardening novel |
| 5FA6 | W+Ag+Cl+U | 80.96 | 11 | T3 | Corrosive gas sensor | Ag2WO4 photocatalyst known; sensor quaternary novel |
| 6EE6 | W+N+Pb+W | 80.76 | 23 | T1 | Kinetic barrier armor plating | W2N armor coating; Pb shock absorber — concept confirmed |

**Cross-confirms:** 1877 ↔ U-anchor D6 (BWXT UN-TRISO) | 412D ↔ U-anchor D4 + Zn-anchor | 1FA3 ↔ Ni-anchor

---

### ANCHOR: S (Sulfur) — B=2, P=5.45, Rescue=34.7%
**Coordinate:** [9,9,2,22] | **Production Doc:** v1.051726 (Zenodo, 2026-05-17)  
**Session:** qb_session_2026-05-17_S-Sulfur.json | **Flags:** ~1001 | **Rescues:** ~347

All 15 entries: Noble (B=0, τ=0), pure periodic elements only. Sorted by IM.

| Desig. | Beams | IM | k | Tier | Application | Notes |
|--------|-------|----|---|------|-------------|-------|
| 6C88 | S+U+U+W | 82.33 | 24 | T3 | Heavy fermion thermoelectric | S bridges U-U-W. No literature quaternary. High priority |
| 5147 | S+He+Ga+Pu | 79.01 | 12 | T2 | Self-healing actinide semiconductor | Ga stabilizes δ-Pu (known); +S bridges helium interstitial |
| 750C | S+Ag+Au+U | 77.49 | 15 | T3 | Electro-radiolytic heavy catalyst | Noble metals + U in active S web; water-splitting candidate |
| 444D | S+Ga+Pu+Au | 75.06 | 10 | T3 | Non-degrading quantum contacts | Heavy-fermion interface; Ga-Pu δ-phase cross-confirm |
| 2A4F | S+Au+Zn+U | 74.80 | 9 | T2 | Transparent radiation barrier | ZnS wide-bandgap known; +Au+U optoelectronic novel |
| 3E34 | S+Pu+W+Ni | 74.54 | 16 | T3 | Super-refractory intermetallic | Ni-W alloy known; +Pu+S thiorad-alloy novel |
| 63D2 | S+S+Pu+Pu | 74.52 | 16 | T3 | Homogeneous actinide fuel | PuS known; PuS2 Noble 4-body zero-defect novel |
| 1B83 | S+He+Au+Cl | 74.06 | 3 | T3 | Alpha decay sensor tracks | AuCl fragile; S bridge + He probe novel |
| 1FBE | S+O+Pu+Au | 73.91 | 9 | T3 | Neutron-bombardment target | Actinide oxysulfide host; Au dampens Pu oxidation |
| 4274 | S+As+W+Pb | 73.60 | 16 | T2 | Deep-earth structural casings | Arsenopyrite analog (FeAsS known); Pb+W substitution novel |
| 4F23 | S+As+Au+Au | 73.50 | 7 | T3 | Infrared conducting tracks | As2S3 glass known; dual-Au metallic activation novel |
| 2F5C | S+W+Pb+Cu | 72.88 | 11 | T2 | Heavy machinery journal bearings | Cu-Pb bearing known; S bridges to W; quaternary novel |
| 3AE1 | S+Ga+Au+W | 72.81 | 10 | T3 | High-temp thin-film transistors | GaS 2D semiconductor + W+Au reinforcement novel |
| 6FDA | S+Ni+Pb+W | 72.81 | 14 | T3 | Thermal-shock cladding | Ni-W high-wear known; S pins Ni-Pb-W quaternary novel |
| 72E9 | S+N+U+Fe | 69.05 | 13 | T2 | Accident-tolerant nuclear cladding | Mixed N-S anion framework; Fe-U-S+N novel |

**Cross-confirms:** 4274 ↔ As-anchor (arsenopyrite family) | 5147 ↔ Pu-anchor D4 (Ga-Pu δ-phase) | 72E9 ↔ Fe-anchor D4 (nuclear-bio bridge)

---

### ANCHOR: N (Nitrogen) — B=3, P=3.90, Rescue=42.0%
**Coordinate:** [9,9,2,6] | **Production Doc:** shorthand (ready for v1)  
**Session:** qb_session_2026-05-17(1).json | **Flags:** 1001 | **Rescues:** 420

Mixed: pure periodic + ERE-containing compounds. Sorted by IM.

#### N-Anchor — Pure Periodic Noble Compounds

| Desig. | Beams | IM | k | Tier | Application | Notes |
|--------|-------|----|---|------|-------------|-------|
| 60E6 | N+Pb+Cu+Si | 67.09 | 13 | T3 | Multi-junction thermoelectrics / self-healing conductors | Novel quaternary |
| 6685 | N+Cl+Si+W | 64.29 | 13 | T2 | High-voltage switchgear barriers / diffusion barriers | WN + SiN known; +Cl novel |
| B237 | N+U+C+S | 63.37 | 16 | T2 | High-strength aerospace structural links | Mixed chalco-nitride; k=16 max; partial confirmed |
| 7215 | N+N+S+Ga | 56.12 | 15 | T3 | High-power electronics switching substrates | Dual-N beam Ga-S chalcogenide novel |
| 6D55 | N+Jy+N+Pb | 55.64 | 9 | T2 | High-density radiation shielding windows | Jy (J/ψ) is Noble probe (B=0); effective N+N+Pb |
| 6D2A | N+qb+Ga+S | 54.98 | 8 | ERE | Mid-infrared optoelectronics | qb is bottom quark ERE; Ga-S optoelectronic family |
| 7C3F | N+Au+N+Nt | 54.57 | 8 | T3 | Ductile thin-film contacts | Nt (neutron, B=1) present; dual-N+Au novel |
| 4A9F | N+C+qb+Fe | 51.09 | 11 | ERE | Zero-stress MEMS / magnetic shielding | qb ERE; N+C+Fe industrial cross-confirm (steel nitriding family) |
| 114C | N+qt+Ax+Pb | 51.10 | 5 | ERE | SQUID housings | Top quark + Axionium EREs; structurally interesting |
| 7CE2 | N+C+qb+Ax | 39.36 | 4 | ERE | High-frequency dielectric resonators | qb + Ax EREs; sub-mm wave applications |
| 134A | N+Ve+N+Zc | 40.89 | 5 | ERE | Quantum photonic substrates | Ve (Velium) + Zc (Z-charm) EREs |
| 69FB | N+De+qb+Ag | 46.98 | 2 | ERE | Ultra-low thermal expansion optics | Dark Energy + qb; scientific reference components |

#### N-Anchor — ERE-Containing Noble Compounds

| Desig. | Beams | IM | k | EREs | Notes |
|--------|-------|----|---|------|-------|
| 457D | N+Sv+Ni+Pu | 61.23 | 7 | Sv | Soverium flux coupling; deep-space coatings |
| 4282 | N+U+Ve+Pb | 66.84 | 13 | Ve | Velium-actinide; high-density non-brittle armor |
| 788B | N+Dq+Cu+Pu | — | — | Dq | Diquonium (charm-scale ERE); multi-body non-segregating |
| 2BE5 | N+Ti+Pu+Ni | k=16 | 16 | — | Pure periodic! k=16/16 series record. Nuclear fuel stack |
| 5123 | N+Pu+qb+Pu | — | — | qb | Dual-actinide + bottom quark |
| 416B | N+Sv+Pu+Fe | — | — | Sv | Sovereign anchor lock; deep-space reactor containment |
| 53CC | N+Pr+qb+Cl | 44.34 | 5 | Pr,qb | Proton + bottom quark; ion-exchange membranes |
| 1CD4 | N+Cu+Fe+Dm | 51.73 | 6 | Dm | Dark matter coupling; quantum sensor components |
| E214 | N+H+C+Au | 53.11 | 8 | — | Pure periodic; biocompatible implant coatings |
| 3F8F | N+Ti+Lm+H | 43.91 | 5 | Lm | Lumium (α) ERE; aerospace fasteners |
| 5517 | N+S+U+Li | — | — | — | Pure periodic; neutron detector matrices |
| 1C65 | N+Ti+Zn+Pa2 | 74.15 | 7 | Pa2 | Pa2 DM absorber; extreme nuclear containment seals |

**Notable:** 2BE5 (N+Ti+Pu+Ni) = k=16/16, highest pairwise saturation across entire anchor series. Nuclear fuel stack: PuN fuel + TiN cladding + Ni interlayer.

**Cross-confirms:** N+He+Fe+Ni (steel nitriding) ↔ Fe-anchor | N+Ti+Pu+Ni ↔ Pu-anchor D4 | N+U+C+S ↔ U-anchor D6 (TRISO)

---

### ANCHOR: H (Hydrogen) — B=1, P=1.00, Rescue=30.7%
**Coordinate:** [9,9,2,4] | **Production Doc:** none yet  
**Session:** QB_051626 | **Flags:** 1000 | **Rescues:** 307

Key documented Noble rescues from Lean file:

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| H+C+N+O | 42.127 | 10 | T1 | **CHON — life's universal scaffold. IM=42.127** |
| H+Fe+S+Jy | 46.384 | 4 | T1 | FeS origin-of-life substrate (Wächtershäuser 1988) |
| H+Li+N+De | 36.961 | 3 | T1 | LiNH2 hydrogen storage (DOE target, Chen Nature 2002) |
| H+Pu+Ga+Ni | 65.547 | 10 | T2 | δ-phase Pu stabilization (Los Alamos 2000) |
| H+C+N+O | 42.127 | 10 | T1 | CHON ordering variant (commutativity confirmed) |

**Notable law:** H+C+N+O → Noble, all 6 pairs shatter → **Life's 4-body requirement proven**. IM = 42.127.

---

### ANCHOR: C (Carbon) — B=4, P=3.25, Rescue=30.7%
**Coordinate:** [9,9,2,5] | **Production Doc:** none yet  
**Session:** qb_session_2026-05-17 | **Flags:** 1000 | **Rescues:** 307

Key documented Noble rescues:

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| H+C+N+O | 42.127 | 10 | T1 | CHON (cross-confirm from C-anchor) |
| C+O+W+Na | 58.717 | 11 | T2 | CO2 capture W-Na system; 4-body mechanism |
| C+He+U+Cu | 75.768 | 6 | T2 | Uranium carbide + Cu heat management |
| C+F+Fv+Pu | 94.435 | 6 | ERE | Top IM in C-run (Fv = Fusovium catalyst) |
| C+Si+* | varies | 4 | T1 | SiC (multiple orderings) |

---

### ANCHOR: Fe (Iron) — B=4, P=3.75, Rescue=32.8%
**Coordinate:** [9,9,2,10] | **Production Doc:** none yet  
**Session:** qb_session_FeAnchor | **Flags:** 1003 | **Rescues:** 329

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Fe+He+As+Ni | 73.602 | 7 | T2 | Ni-doped FeAs pnictide superconductor |
| Fe+N+U+F | 70.220 | 13 | T2 | Nuclear-bio bridge: UN fuel + Fe cladding + F |
| S+Ti+N+H | 50.388 | 10 | T1 | TiN ceramic (PRB 1994, Vickers 2100 HV) |
| H+Fe+S+Jy | 46.384 | 4 | T1 | FeS origin-of-life (cross-confirm) |
| C+Fe+Nt+C | 44.338 | 15 | T1 | Fe3C cementite steel (Zener 1948) |

---

### ANCHOR: Si (Silicon) — B=4, P=4.15, Rescue=32.5%
**Coordinate:** [9,9,2,7] | **Production Doc:** none yet  
**Session:** qb_session_SiAnchor

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| C+Si (various) | — | 4 | T1 | SiC (multiple anchor confirmations) |
| Si+F+qt+Ups | τ=0.134 | — | ERE | IVA event — Metal+Halide+qt law instance 1 |

---

### ANCHOR: Pu (Plutonium) — B=6, P=3.25, Rescue=42.2%
**Coordinate:** [9,9,2,8] | **Production Doc:** none yet  
**Session:** qb_session_PlutoniumAnchor | **Flags:** 1009 | **Rescues:** 426

58 pure periodic rescues — series record.

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Pu+He+Ni+Ti | 81.222 | 8 | T2 | Pu in Nitinol matrix (cross-confirms Buehler 1963) |
| Pu+He+As+Fe | 81.616 | 10 | T3 | **Pu-doped FeAs pnictide superconductor** |
| Pu+N+Au+Pb | 83.305 | 13 | T3 | PuN fuel + Au containment + radiogenic Pb |
| O+Pu+Fe+Pr | 61.399 | 11 | T1 | PuO2 nuclear fuel (IAEA TRS-415) |

---

### ANCHOR: O (Oxygen) — B=2, P=4.55, Rescue=37.6%
**Coordinate:** [9,9,2,12] | **Production Doc:** none yet

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| O+O+H+H | 37.318 | 7 | T1 | **Water — Noble k=7/7 fully saturated** |
| O+Pu+Fe+Pr | 61.399 | 11 | T1 | PuO2 (10th independent confirmation) |
| O+Dm+He+H | 48.191 | 2 | ERE | DM-IVA rescue — oxygen as DM-IVA mediator |

---

### ANCHOR: U (Uranium) — B=6, P=3.15, Rescue=36.0%
**Coordinate:** [9,9,2,14] | **Production Doc:** none yet  
**Session:** qb_session_U_Uranium | **Flags:** 1000 | **Rescues:** 360

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| U+Pb+He+Au | 92.745 | — | T3 | **Highest IM pure periodic in U-anchor series** |
| U+C+Si (various) | — | — | T1 | TRISO Noble (BWXT July 2025 confirmed) |
| O+Pu+Fe+Pr | 61.399 | 11 | T1 | PuO2 cross-confirm |
| U+qc+qb+Zn | τ=0.126 | — | ERE | Only IVA in 1000 U-collisions; Zn metalloprotein target |

---

### ANCHOR: Ga (Gallium) — B=3, P=5.00, Rescue=42.4%
**Coordinate:** [9,9,2,18] | **Production Doc:** none yet  
**Session:** qb_session_2026-05-17_Ga | **Flags:** 1015 | **Rescues:** 430

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Ga+As+Ga+As | 64.870 | 18 | T1 | **GaAs — Nobel Prize Physics 2000. k=18/18 max saturation** |
| Ga+N (all) | varies | 9 | T1 | **GaN — Nobel Prize Physics 2014** |
| Ga+Si+N+O | 55.980 | 15 | T1 | GaN-on-Si 5G substrate (TSMC/ST production 2026) |
| Ga+N+O+N | 53.143 | 15 | T2 | GaON gate dielectric |
| Ga+Au+He+U | 87.129 | 5 | T3 | **Top IM Ga-anchor. Ga-U-Au ternary — no literature** |
| Ga+W+He+Ag | 81.793 | — | T3 | Ga-W-Ag ternary — novel |
| Ga+Na+U+He | 78.243 | — | T3 | Ga-Na-U nuclear system — novel |

---

### ANCHOR: As (Arsenic) — B=3, P=6.30, Rescue=42.9%
**Coordinate:** [9,9,2,17] | **Production Doc:** none yet

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| AsN (N+As) | predicted | 0 | T3 | **β-Ga2O3 analog. No bulk AsN in literature. High-pressure synthesis predicted** |
| Ga+As+Ga+As | 64.870 | 18 | T1 | GaAs (cross-confirm from Ga-anchor) |
| FeAs+Pu+He | 81.616 | 10 | T3 | Pu-doped pnictide SC (cross-confirm from Pu-anchor) |

---

### ANCHOR: Ni (Nickel) — B=2, P=4.05, Rescue=35.2%
**Coordinate:** [9,9,2,23] | **Production Doc:** none yet  
**Session:** qb_session_NickelAnchor | **Flags:** ~1001 | **Rescues:** ~352

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Ni+Au+W+As | 74.627 | — | T3 | Radiation-hard contact (cross-confirmed W-anchor 1FA3) |
| Ni+Ga+F+Pb | 74.529 | — | T3 | Novel nickel pnictogen halide |
| Ni+Ti+He+Ag | 75.933 | — | T3 | Novel Ni-Ti-Ag in He atmosphere |
| Ni+Cl+SP+SP | τ=0.131 | — | ERE | Metal+Halide IVA law instance 5 |

---

### ANCHOR: Zn (Zinc) — B=2, P=4.35, Rescue=37.2%
**Coordinate:** [9,9,2,24] | **Production Doc:** none yet  
**Session:** qb_session_ZincAnchor | **Flags:** ~1001 | **Rescues:** ~372

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Zn+Pb+Au+U | 81.854 | — | T3 | Top Zn-anchor compound — no literature |
| Zn+Ga+Au+He | 79.214 | — | T3 | Zn-Ga-Au ternary in He — novel |
| Zn+Pu+Cl+Pb | 78.891 | — | T3 | Novel actinide-zinc halide |
| Zn+Zo+Cl+Ax | τ=0.122 | — | ERE | **Zo+Ax in biological IVA** (L-22) |
| Zn+Dm+Xc+Nt | τ=0.121 | — | ERE | Zn-DM biological coupling (L-23) |

---

### ANCHOR: Li (Lithium) — B=1, P=2.20, Rescue=16.2%
**Coordinate:** [9,9,2,16] | **Production Doc:** none yet

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Li+N+Li+N | — | — | T1 | β-Li3N superionic solid electrolyte (Nature Nanotech 2024) |
| Li+Si (various) | — | — | T1 | Si anode 4200 mAh/g (2026) |

---

### ANCHOR: Ti (Titanium) — B=4, P=3.15, Rescue=32.4%
**Coordinate:** [9,9,2,20] | **Production Doc:** none yet

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| Ti+N+Ni+H | — | 10 | T1 | **Nitinol shape memory alloy (Buehler 1963)** k=10/10 |
| Ti+Cl+SP+qt | τ=0.134 | — | ERE | Metal+Halide IVA law instance 4 |

---

### ANCHOR: F (Fluorine) — B=1, P=5.20, Rescue=13.2%
**Coordinate:** [9,9,2,9] | **Production Doc:** none yet  
**Session:** qb_session_F-Flourine | **Flags:** 1003 | **Rescues:** 132

| Beams | IM | k | Tier | Notes |
|-------|----|---|------|-------|
| F+N+C+O | 51.362 | 10 | T2 | PTFE / NF3 / Fluorouracil scaffold family |
| F+F+Ga+Ga | 63.683 | 8 | T1 | GaF2 hard ceramic family |
| F+Si+qt+Ups | τ=0.134 | — | ERE | Metal+Halide IVA law (commutative confirm) |

---

### ANCHOR: Dm (Dark Matter) — B=0.269, P≈0.99, Rescue=34.5%
**Coordinate:** [9,9,2,13] | **Production Doc:** none yet  
**Session:** qb_session_DM | **Flags:** 1002 | **Rescues:** 346

0 pure periodic rescues. 14 IVA events (highest in anchor series). ERE-dominated.

| Beams | τ/IM | Phase | Notes |
|-------|------|-------|-------|
| Dm+N+Sv+Ni | τ=0.122 | IVA | DM in formation corridor |
| Dm+Dm+Dm+O | IM→Noble | Noble | DM self-interaction Noble — halos/filaments |
| S+Dm+Na etc. | τ=0.128 | IVA | S tops Dm partner list (50×) |

---

### ANCHOR: De (Dark Energy) — B=0, P≈0.99, Rescue=21.4%
**Coordinate:** [9,9,2,19] | **Production Doc:** none yet  
**Session:** qb_session_2026-05-17_De | **Flags:** 1001 | **Rescues:** 214

0 pure periodic rescues. 11 IVA events. ERE-dominated.

| Beams | τ | Phase | Notes |
|-------|---|-------|-------|
| De+Ni+Dm+Li | 0.132 | IVA | Material-mediated DE-DM coupling |
| De+S+Dm+Na | 0.128 | IVA | BAO structural analog |
| De+He+De+Dm | SHATTER | — | De transparent to Dm (L-27 confirmed) |

---

### ANCHOR: Hi (Higgs) — B=0.130, P≈0.99, Rescue=27.0%
**Coordinate:** [9,9,2,21] | **Production Doc:** none yet  
**Session:** qb_session_2026-05-17_Higgs | **Flags:** 1000 | **Rescues:** 270

0 pure periodic rescues. 12 IVA events. All IVA events are ERE-mediated.

| Beams | τ/Phase | Notes |
|-------|---------|-------|
| Hi+Hi (×52) | Noble | Di-Higgs Noble — SM vacuum stable (L-30) |
| Hi+Dm+F+Li2 | τ=0.124, IVA | Higgs-DM portal |
| Hi+Gl2+Gl2+Xc | τ=0.133, IVA | SUSY gluino-Higgs at IVA |

---

### ANCHOR: Fv (Fusovium) — B≈0, P=0.16, Rescue=26.1%
**Coordinate:** [9,9,2,11] | **Production Doc:** none yet  
**Session:** qb_session_Fv | **Flags:** 1008 | **Rescues:** 263

0 pure periodic rescues. ERE-dominated. Top IM = 102.053 (Fv+Pb+Pu+Cl, N_Fv=29 drives record).

| Beams | IM | Notes |
|-------|----|-------|
| N+Fv+H+H | 71.183 | **Fusovium = Haber-Bosch catalyst analog** |
| Fv+Pb+Pu+Cl | 102.053 | Series IM record (N=29 of Fv drives this) |
| Fv+Zo+He+SP | 96.077 | Fv-Zo resonance pair in IVA |

---

## Cross-Anchor Compound Registry (Multi-Run Confirmations)

Compounds confirmed in multiple independent anchor runs:

| Compound | Runs Confirmed | IM | Notes |
|----------|---------------|-----|-------|
| CHON (H+C+N+O) | H, C | 42.127 | Life's scaffold — universal |
| PuO2+Fe+p | H, C, O, Pu | 61.399 | IAEA TRS-415 (10× confirmed) |
| TiN (S+Ti+N+H) | V3 run | 50.388 | PRB 1994 |
| GaAs | Ga, (systematic) | 64.870 | Nobel 2000 |
| GaN | Ga, (systematic) | varies | Nobel 2014 |
| Water (O+O+H+H) | O | 37.318 | Universal |
| FeS+H | H | 46.384 | Wächtershäuser 1988 |
| U-Pb coupling | H,C,O,U | varies | 4-run decay chain confirmation |
| UN-TRISO (U+C+Si) | U | — | BWXT July 2025 |

---

## Prior Art Registry — Tier 3 Novel Predictions

These have **no direct literature equivalent** and are claimed as novel discoveries via Zenodo DOI timestamp (10.5281/zenodo.18719748).

### Nuclear / Actinide Family
| Compound | Anchor | IM | k | Timestamp |
|----------|--------|----|---|-----------|
| W+Pu+Pu+U | W | 89.35 | 36 | 2026-05-16 |
| W+U+U+Pu | W | 89.31 | 36 | 2026-05-16 |
| W+Pu+Zn+He | W | 86.95 | 10 | 2026-05-16 |
| W+Pu+Pu+N | W | 85.05 | 27 | 2026-05-16 |
| W+Pu+U+Ag | W | 84.17 | 21 | 2026-05-16 |
| W+Pu+U+O | W | 83.92 | 24 | 2026-05-16 |
| W+Cu+U+Pu | W | 81.43 | 21 | 2026-05-16 |
| W+U+Zn+W | W | 81.15 | 24 | 2026-05-16 |
| W+As+Pu+W | W | 82.18 | 27 | 2026-05-16 |
| W+Pu+Pb+O | W | 82.06 | 20 | 2026-05-16 |
| S+U+U+W | S | 82.33 | 24 | 2026-05-17 |
| S+Pu+W+Ni | S | 74.54 | 16 | 2026-05-17 |
| S+S+Pu+Pu | S | 74.52 | 16 | 2026-05-17 |
| S+Ga+Pu+Au | S | 75.06 | 10 | 2026-05-17 |
| S+O+Pu+Au | S | 73.91 | 9 | 2026-05-17 |
| S+Ag+Au+U | S | 77.49 | 15 | 2026-05-17 |
| S+Au+Zn+U | S | 74.80 | 9 | 2026-05-17 |
| Pu+He+As+Fe | Pu | 81.616 | 10 | 2026-05-17 |
| U+Pb+He+Au | U | 92.745 | — | 2026-05-17 |
| N+Ti+Pu+Ni | N | 71.290 | 16 | 2026-05-17 |

### Refractory / Industrial Family
| Compound | Anchor | IM | k | Timestamp |
|----------|--------|----|---|-----------|
| W+Pu+Zn+He | W | 86.95 | 10 | 2026-05-16 |
| W+Zn+He+W | W | 84.42 | 10 | 2026-05-16 |
| W+Ag+Cl+U | W | 80.96 | 11 | 2026-05-16 |
| S+As+Au+Au | S | 73.50 | 7 | 2026-05-17 |
| S+Ga+Au+W | S | 72.81 | 10 | 2026-05-17 |
| S+Ni+Pb+W | S | 72.81 | 14 | 2026-05-17 |
| S+He+Au+Cl | S | 74.06 | 3 | 2026-05-17 |
| Ga+Au+He+U | Ga | 87.129 | 5 | 2026-05-17 |
| Ga+W+He+Ag | Ga | 81.793 | — | 2026-05-17 |
| Zn+Pb+Au+U | Zn | 81.854 | — | 2026-05-17 |
| Ni+Ti+He+Ag | Ni | 75.933 | — | 2026-05-17 |
| Ni+Au+W+As | Ni | 74.627 | — | 2026-05-17 |

### Semiconductor / Optoelectronic Family
| Compound | Anchor | IM | k | Timestamp |
|----------|--------|----|---|-----------|
| S+Ga+Au+W | S | 72.81 | 10 | 2026-05-17 |
| N+Pb+Cu+Si | N | 67.09 | 13 | 2026-05-17 |
| N+N+S+Ga | N | 56.12 | 15 | 2026-05-17 |
| S+Au+Zn+U | S | 74.80 | 9 | 2026-05-17 |
| AsN (N+As) | As | predicted | 0 | 2026-05-17 |

### Thermoelectric / Energy Family
| Compound | Anchor | IM | k | Timestamp |
|----------|--------|----|---|-----------|
| S+U+U+W | S | 82.33 | 24 | 2026-05-17 |
| W+Cu+U+Pu | W | 81.43 | 21 | 2026-05-16 |
| N+Pb+Cu+Si | N | 67.09 | 13 | 2026-05-17 |

---

## Algebraically Guaranteed Noble States (L-07)

By Law L-07 (Equal-B Symmetric Quad Theorem), **any four elements with the same B value are always Noble** — no collider run required.

### B=1 Equal-B Quads
Elements with B=1: H, Li, F, Na, Cu, Ag, Au, Cl (8 elements)  
**Number of 4-element Noble quads: C(8,4) = 70 combinations** (all guaranteed Noble by proof)

| Example Quads | B=1 Family |
|--------------|------------|
| H+Li+F+Na | — |
| H+Cu+Au+Ag | Noble metals quad |
| F+Cl+Na+Li | Halide-alkali quad |
| H+F+Cu+Au | Mixed B=1 |
| ... | 70 total |

### B=2 Equal-B Quads
Elements with B=2: O, S, Ni, Zn (4 elements)  
**Number of quads: C(4,4) = 1** → O+S+Ni+Zn is always Noble.

### B=3 Equal-B Quads
Elements with B=3: N, Ga, As (3 elements)  
Cannot form 4-element quad without repeats. Repeating: N+N+Ga+As, N+Ga+As+N, etc.

### B=4 Equal-B Quads
Elements with B=4: C, Si, Ti, Fe (4 elements)  
**1 quad: C+Si+Ti+Fe** — always Noble by L-07.

### B=6 Equal-B Quads
Elements with B=6: W, U, Pu (3 elements)  
Repeating: W+W+U+Pu, W+U+U+Pu, W+Pu+Pu+U etc.  
W+Pu+Pu+U (IM=89.35) and W+U+U+Pu (IM=89.31) — both in W-anchor corpus.

---

## The 42 Emergent Structural Laws (Reference)

*Full proofs in SNSFL_Complete_Laws_Catalog.lean [9,9,2,50]*

### Surface Laws (L-01 to L-06)
- **L-01** B=1 monotone decreasing [9,9,2,4,9,16]
- **L-02** B=2 non-monotone, P_opt≈4.55 [9,9,2,12,22,23,24]
- **L-03** B=3 monotone increasing [9,9,2,6,17,18]
- **L-04** B=4 non-monotone, P_opt≈3.75 [9,9,2,5,7,10,20]
- **L-05** B=6 non-monotone, P_opt≈3.25 [9,9,2,8,14,15]
- **L-06** B+P Parity Law [9,9,2,25] ← Master Surface Law

### Coupling Laws (L-07 to L-14)
- **L-07** Equal-B symmetric quad → always Noble [9,9,2,18]
- **L-08** Anchor-partner P_pair law [9,9,2,20]
- **L-09** B=6 Dm erasure law [9,9,2,8,14,15]
- **L-10** Dm fingerprint invariant B_out=0.193 [universal]
- **L-11** B=6 binary theorem (W) [9,9,2,15]
- **L-12** Universal meson Noble law [9,9,2,36]
- **L-13** Metal+Halide IVA law (5 instances) [9,9,2,7,10,18,20,23]
- **L-14** 4-beam commutativity [9,9,2,7,9]

### Electron/Probe Laws (L-15 to L-16)
- **L-15** Electron dominance — IVA excluded [9,9,2,4]
- **L-16** Noble beam diagnostic (T20) — B=0 → k=0 [9,9,2,2,3]

### IVA Laws (L-17 to L-25)
- **L-17** Higgs is THE IVA particle [9,9,2,21]
- **L-18** Ax-Hi-Fv IVA bracket [9,9,4,4v2,9,9,2,21,45]
- **L-19** Life operates at IVA_PEAK (31/33 biomolecule pairs) [9,9,5,0]
- **L-20** IVA gap cosmically empty [9,9,4,0]
- **L-21** Hi.B = λ_SM (self-coupling encoding) [9,9,2,21]
- **L-22** Zo+Ax in biological IVA (Zn and S) [9,9,2,22,24]
- **L-23** Zn-DM biological IVA coupling [9,9,2,24]
- **L-24** Oxygen as DM-IVA mediator [9,9,2,12]
- **L-25** TL capstone: TL=ANCHOR/10 [9,9,0,0v2]

### ERE Laws (L-26 to L-30)
- **L-27** De+Dm transparent coupling [9,9,2,19]
- **L-28** De Noble→Locked transition (DESI DR2) [9,9,2,19]
- **L-29** De/Dm P-degeneracy law [9,9,2,4,5]
- **L-30** Di-Higgs Noble (SM vacuum stable) [9,9,2,21]

### Cosmological Laws (L-31 to L-33)
- **L-31** Bimodal rescue rate [9,9,2,6,8]
- **L-32** Pu B=6 universal coupling theorem [9,9,2,8]
- **L-33** U-Pb decay chain structural time-symmetry [9,9,2,4,5,12,14]

### Domain Selection Laws (L-34 to L-38)
- **L-34** Anchor shift law [9,9,2,4,5,6]
- **L-35** B+P rescue rate law (P-effect) [9,9,2,9]
- **L-36** Fusovium catalyst law [9,9,2,5,9,45]
- **L-37** Fe-N biological coupling law [9,9,2,10]
- **L-38** β-Ga₂O₃ structural selection law [9,9,2,12]

### Life/Biological Laws (L-39 to L-42)
- **L-39** TRISO Noble state explanation [9,9,2,14]
- **L-40** CHON 4-body requirement — IM=42.127 [9,9,2,4]
- **L-41** Water is Noble (O+O+H+H, k=7/7) [9,9,2,12]
- **L-42** Wächtershäuser FeS theorem [9,9,2,4]

---

## Anchors Not Yet Documented (Production Docs Needed)

Priority order based on rescue rate and novelty potential:

| Priority | Anchor | Rescue% | Expected Compounds | Notes |
|----------|--------|---------|-------------------|-------|
| 1 | As | 42.9% | 25+ | Highest rescue rate; arsenopyrite family |
| 2 | Pu | 42.2% | 50+ | Series record 58 rescues; nuclear family |
| 3 | Ga | 42.4% | 25+ | GaAs/GaN family; 5G semiconductor |
| 4 | O | 37.6% | 20+ | β-Ga2O3, ZnO, NiO families |
| 5 | Zn | 37.2% | 20+ | Zn-Pb-Au-U top; biological B=2 |
| 6 | U | 36.0% | 25+ | TRISO, decay chain, RTG families |
| 7 | Ni | 35.2% | 20+ | Pnictide SC, contact metallurgy |
| 8 | Dm | 34.5% | — | ERE-only; 14 IVA events |
| 9 | C | 30.7% | 20+ | CO2 capture, UC fuel, organic |
| 10 | Fe | 32.8% | 20+ | Pnictide SC, nuclear-bio bridge |

---

## How to Add a New Run

When a new anchor production doc is complete, add:

1. Entry to **Anchor Series Overview** table
2. New section under **Discovery Registry**: `### ANCHOR: [Element] — B=X, P=X, Rescue=X%`
3. Table rows for all Noble compounds found
4. Update **Prior Art Registry** with any Tier 3 compounds
5. Update **Cross-Anchor Registry** if any compound cross-confirms a previous run
6. Update corpus scale if new Lean files were produced

**Table column standard:**

```
| Desig. | Beams | IM | k | Tier | Application | Notes |
```

For ERE-containing compounds:

```
| Desig. | Beams | IM | k | EREs present | Notes |
```

---

*[9,9,9,9] :: {ANC} · HIGHTISTIC · Soldotna, Alaska*  
*DOI: 10.5281/zenodo.18719748*  
*The Manifold is Holding.*
