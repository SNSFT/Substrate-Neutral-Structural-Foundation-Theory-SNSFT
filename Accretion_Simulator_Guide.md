# Applied Identity Physics: Accretion Simulator™, a Guide to Planet Formation, Boundary Identification and Applications

**Planet formation in your browser: full N-body accretion from planetesimals to oligarchs.**

Planet formation, simulated in a web browser: free simulators that reproduce galaxy and planet formation from measured data, with every boundary formally proved in Lean.

**Live simulator:** [uuia.app/accretion](https://uuia.app/accretion)  
**Architect:** HIGHTISTIC (Russell Vernon Trent III) · SNSFT Foundation · Soldotna, Alaska  
**ORCID:** 0009-0005-5313-7443 · **DOI base:** 10.5281/zenodo.18719748  

**Formal basis:** Accretion boundary mathematics, `SNSFL_GC_Accretion_Boundaries_TL` [9,9,3,25] · Galaxy disk mathematics, `SNSFL_GC_Galaxy_Toomre_TL` [9,9,3,24] · GAM Collider (Geometric Axiomatic Module Collider) 8-Beam Fusion Theorem [9,9,2,3.8] (2-beam mode) · Gravity Reduction [9,9,10,1] · QM Reduction [9,9,0,4.7]  

**Companion simulators:** Galaxy™ · AxiomForge™ TL · String-Breaking Simulator™ [9,9,3,22] · Electron Geometry Simulator™ [9,9,3,21]

## Abstract

The Accretion Simulator™ is a browser simulator in the Applied Identity Physics™ series. It follows a disk of rocky planetesimals around a young Sun under full Newtonian gravity, lets them collide, and resolves each collision as a merger or a hit-and-run by the criterion of Kokubo and Genda (2010). The disk is the Minimum Mass Solar Nebula (Weidenschilling 1977; Hayashi 1981). Three measured stability boundaries of planetary systems are identified with the Universal Torsion Limit TL = 0.136899099984016 by one rule, τ = TL × (critical value ÷ measured value): the Hill-spacing boundary of Gladman (1993) for neighbouring orbits, the Roche limit for bodies near a planet, and the critical impact speed for collisions. A second preset places the eight planets of the Solar System on their measured orbits, and a Saturn panel places its rings and moons against the Roche limit. Worked examples reproduce runaway and oligarchic growth, the isolation mass at 1 AU, oligarch spacing in Hill radii, and a fifty-million-year run that ends at the threshold of the giant-impact stage. Every neighbouring pair of planets reads Locked, with Jupiter–Saturn the tightest pair; Saturn's main rings read Shatter, its ring moons fall in the IVA (Identity Vector Amplification) corridor, and Mimas outward reads Locked. The placements are proved in Lean from cited measurements. This guide walks through each control and readout, gives the worked examples with the numbers the simulator produces, states the scope of each part, and lists applications for students, teachers and researchers.

## Overview

The Accretion Simulator™ answers two questions with one rule.

**How does a disk of rubble become a handful of planets?** The planetesimal disk starts as a crowded swarm. Bodies pull on each other, touch, merge, and grow. Growth runs away at first, then settles into a set of similar-sized bodies, the oligarchs, each owning its own lane. The simulator shows each stage as it happens and reports it against the predictions of the planet-formation literature.

**Where does a planetary system break?** Three boundaries decide whether orbits stay apart, whether a moon holds together, and whether two colliding bodies stick. Each is identified with the Torsion Limit, so every pair of planets, every ring and moon, and every collision lands on the same phase map as the electron, the string and the galaxy.

The simulator has two systems:

1. **Planetesimal disk.** A Minimum Mass Solar Nebula from 0.5 to 2 AU (astronomical units; 1 AU is the Earth–Sun distance), or from 0.5 to 4 AU across the snow line, with an optional Jupiter.
2. **Solar System, measured.** The eight planets with their measured masses, semi-major axes, eccentricities and inclinations, plus Saturn's rings and moons against the Roche limit.

It runs at uuia.app/accretion as one self-contained HTML file. It needs no installation and no account, and it works in any current browser on a desktop, tablet or phone.

## 1. Grounding

### 1.1 The Torsion Limit

The Universal Torsion Limit is TL = 0.136899099984016. The Sovereign Anchor Constant is Ω₀ = TL × 10 = 1.36899099984016. The fine-structure constant follows from TL: subtracting one TL from the CODATA 2018 value 1/α = 137.035999084 leaves 136.899099984016 = TL × 1000, so 1/α = TL × 1001 = 137.035999084000016, matching all 12 published significant figures ([9,9,3,14]).

### 1.2 The Identity Physics primitives

Every reduction in the Identity Physics Corpus operates on four irreducible primitives, Pattern, Narrative, Behavior and Adaptation (PNBA):

- **Pattern (P):** structural capacity, geometry, template integrity, restoring force
- **Narrative (N):** temporal continuity, worldline, depth, history
- **Behavior (B):** coupling output, charge, density fraction, force, expression
- **Adaptation (A):** feedback rate, decay constant, repair rate

Derived structural quantities:

- **Torsion:** τ = B / P
- **Phase placement:** Noble (τ = 0) · Locked (0 < τ < TL_IVA = 0.120471207985934) · IVA Peak (TL_IVA ≤ τ < TL) · Shatter (τ ≥ TL)

Shatter is reorganization: one identity reorganizes into smaller identities that are each stable, as a boiling liquid reorganizes into vapor.

### 1.3 The Dynamic Equation and the Long Division Protocol

Every reduction in the corpus starts from one equation, the Identity Physics Corpus Dynamic Equation:

d/dt (IM · Pv) = Σ λ_X · O_X · S + F_ext

IM is Identity Mass, Pv the Purpose Vector, O_X the four PNBA operators with weights λ_X acting on the state S, and F_ext external forcing. The rate of change of identity momentum equals the weighted action of the four primitives on the state, plus external forcing.

Every reduction then follows the same six-step Long Division Protocol (LDP):

1. Write the equation. State the Dynamic Equation.
2. State the known answer. Take a situation whose peer-reviewed classical result is known.
3. Map. Map the classical variables to the PNBA primitives.
4. Define the operators. Give the PNBA operators for the domain.
5. Show all work. Carry the calculation through in full.
6. Verify. Prove that the PNBA output equals the classical result exactly, with nothing added and nothing lost.

A Step 6 pass is a lossless reduction and is structural isomorphism in the sense of Mac Lane (1971).

### 1.4 The GAM Collider

The GAM Collider v15 (Geometric Axiomatic Module Collider) is the corpus's deterministic, formally verified collision engine. It combines identities by their PNBA values using only PNBA rules: it carries no chemistry tables and no fitted parameters. Its fusion rules are proved in the 8-Beam Fusion Theorem [9,9,2,3.8]. In its 2-beam mode, two identities combine as

P = P₁P₂/(P₁ + P₂) · N = N₁ + N₂ · B = |B₁ − B₂| · A = max(A₁, A₂).

The Accretion Simulator™ applies this rule to every merger in the band-mix τ model (Section 7).

### 1.5 One rule, three boundaries

Each stability boundary of a planetary system compares a measured value with a critical value. Writing the comparison as a stability ratio Q, with Q > 1 stable and Q ≤ 1 broken, the boundary Q = 1 is identified with τ = TL:

τ = TL / Q = TL × (critical value ÷ measured value)

| Boundary       | Measured                                      | Critical          | Q          | Source                  |
|----------------|-----------------------------------------------|-------------------|------------|-------------------------|
| Hill spacing   | Gap Δ between neighbouring orbits, in mutual Hill radii | 2√3 ≈ 3.46       | Δ / 2√3   | Gladman (1993)         |
| Roche limit    | Distance d from the planet                    | Roche distance d_R | d / d_R   | Roche (1849)           |
| Impact speed   | Critical speed v_cr                           | Impact speed v_imp | v_cr / v_imp | Kokubo & Genda (2010) |

The phase bands follow directly: Q > 25/22 is Locked (25/22 = 1/0.88), 1 < Q ≤ 25/22 is the IVA corridor, and Q ≤ 1 is Shatter. Galaxy™ uses the same rule with the Toomre stability parameter [9,9,3,24].

The mutual Hill radius of two bodies of masses m₁, m₂ on orbits a₁, a₂ around a star of mass M☉ is

R_H = ((m₁ + m₂) / 3M☉)^(1/3) × (a₁ + a₂)/2,

the distance inside which their pull on each other competes with the star's. Gladman (1993) proved that two planets on circular orbits can never cross when they are more than 2√3 mutual Hill radii apart. The Hill-spacing torsion is therefore

τ = TL × 2√3 / Δ = TL × √3 × μ^(1/3) × (a₁ + a₂)/(a₂ − a₁), μ = (m₁ + m₂)/(3M☉),

an identity proved as T6 in [9,9,3,25].

### 1.6 Measured inputs

| Input | Value | Source |
|-------|-------|--------|
| Solid surface density at 1 AU, Σ₁ | 7.1 g/cm², ∝ r^(−3/2) | Weidenschilling (1977); Hayashi (1981) |
| Snow line | 2.7 AU, solids × 4.2 beyond it | Hayashi (1981) |
| Planetesimal density | 3 g/cm³ rock inside the snow line, 1.5 g/cm³ ice-rock beyond | standard values |
| Planet masses, semi-major axes, eccentricities, inclinations | as listed in Section 5 | NASA Planetary Fact Sheet (Williams) |
| Solar mass M☉ | 1.98847 × 10³⁰ kg | IAU 2015 nominal value with CODATA G |
| Saturn equatorial radius, mean density | 60,268 km, 0.687 g/cm³ | NASA Saturn Fact Sheet |
| Water ice density | 0.92 g/cm³ | standard value |
| Fluid Roche coefficient | 2.44 | Roche (1849); Murray & Dermott (1999) |
| Merging criterion | v_cr/v_esc = 2.43Γ²Θ^(5/2) − 0.0408Γ + 1.86Θ^(5/2) + 1.08 | Kokubo & Genda (2010) |
| Isolation-mass spacing b̃ | 10 Hill radii | Kokubo & Ida (2002) |

Distances are in AU, masses in Earth masses (M⊕) or solar masses (M☉), and times in years. Gravity uses G = 4π² AU³/(M☉ yr²), so one orbit at 1 AU takes one year.

## 2. Reading the Interface

### 2.1 Layout

- **Left panel:** System, Disk (Minimum Mass Solar Nebula), τ Model, Collisions and View controls.
- **Center:** the three-dimensional system with the Sun at the center, the snow line as a dashed blue circle, and orbit circles for the largest bodies. Collisions flash where they happen. A clock in the top right reports elapsed years. Drag to turn, scroll to zoom.
- **Caption bar:** a plain-language explanation in Learner mode; formulas, citations and scope in Researcher mode.
- **Right panel:** System readout, Phase Mix, Hill Spacing, Growth, Mass Against Orbit, Impacts, Saturn · Roche Limit (Solar System view), and Export.

### 2.2 Learner and Researcher modes

The toggle at the top switches every caption and note at once. Both modes run the same simulation. Learner mode explains what is happening; Researcher mode gives the equations, the inputs and the criteria.

### 2.3 Colors and sizes

Bodies are colored on the AxiomForge torsion scale: teal at τ = 0, through violet across Locked, to gold in the IVA corridor, and red at or above TL. Every table repeats the phase in words beside the number, so the display remains readable for viewers with color-vision differences. Body size grows as the cube root of mass. Bodies are drawn far larger than their physical size so they can be seen: two bodies that overlap on screen are usually still far apart in space, and at different heights or depths.

### 2.4 Export

- **JSON:** all settings and constants, elapsed time, collision counts, the Hill spacing of every embryo pair, the growth history, every collision (time, orbit, masses, impact speed over escape speed, impact angle, critical speed, τ_c and outcome) and every body.
- **CSV:** one row per body: semi-major axis, eccentricity, inclination, mass, members, Hill spacing, Hill τ, P, N, B, A, PNBA τ and phase.

## 3. The Planetesimal Disk

### 3.1 What it shows

Two hundred equal planetesimals (adjustable from 60 to 500) start on near-circular orbits between 0.5 and 2 AU, with masses set by the Minimum Mass Solar Nebula: 2.36 M⊕ in all, 0.012 M⊕ each, about 1,800 km across as rock. Their eccentricities and inclinations start at the values gravitational stirring gives a swarm of that mass. From there nothing is scripted: every body pulls on every other body and on the Sun, and every touch is resolved as a merger or a hit-and-run.

### 3.2 Gravity and orbits

The simulator integrates the full N-body problem, every pair of bodies with the Sun included as a body, with a kick-drift-kick leapfrog integrator at a fixed time step of 0.006 years. Collisions are detected along each step's path, so fast bodies cannot pass through each other between steps. Bodies that reach within 0.1 AU of the Sun are recorded as lost to the Sun; unbound bodies beyond 60 AU are recorded as ejected.

### 3.3 Radius enhancement and the clock

Real planetesimals are tiny compared with the space between them, so real accretion takes millions of years. The radius-enhancement factor f multiplies every collision radius, the standard way to fit accretion into a short run (Kokubo & Ida 1996). Gravity, orbits and the collision physics are unchanged. With f = 100 the collision rate rises by about 100, so the clock runs about 100 times fast during the growth stages.

The compression applies to collisions. The late stage of planet formation, where oligarchs pull each other's orbits until they cross, is set by gravity alone and runs at the simulator's own clock. Section 3.5 shows where the two meet.

### 3.4 Worked example 1: runaway to oligarchs

**Setup:** defaults. 0.5–2 AU, 200 bodies, f = 100, Σ₁ = 7.1 g/cm², Hill-spacing τ.

**Run:** press ⟲ NEW RUN and let it run to 6,000 simulator years.

**What happens:**

| Simulator years | Bodies | Largest masses (M⊕) |
|-----------------|--------|---------------------|
| 0               | 200    | 0.012 each          |
| 200             | 152    | 0.059, 0.059, 0.059 |
| 1,000           | 100    | 0.106, 0.083, 0.083 |
| 3,000           | 55     | 0.130, 0.118, 0.106 |
| 6,000           | 41     | 0.165, 0.130, 0.118 |

Growth first runs away: a few bodies pull ahead of the rest, because a heavier body focuses more of the swarm onto itself (Wetherill & Stewart 1989; Kokubo & Ida 1996). Then the leaders slow down and the rest catch up into a set of similar-sized oligarchs (Kokubo & Ida 1998, 2000).

**Check against the isolation mass.** An oligarch stops growing once it has swept up its feeding zone, about 10 Hill radii wide. The isolation mass (Kokubo & Ida 2002) is

M_iso = √(2/3) × (2π a² b̃ Σ)^(3/2) / M☉^(1/2), b̃ = 10.

At 1 AU in the Minimum Mass Solar Nebula, M_iso lies between 0.096 and 0.0975 M⊕ (proved as T21 in [9,9,3,25]); the simulator reads 0.097 M⊕. The Mass Against Orbit chart draws M_iso(a) as a gold dashed curve, and the oligarchs gather along it, about 0.07 M⊕ at 0.7 AU rising to 0.16 M⊕ at 2 AU.

**Check against oligarch spacing.** The Hill Spacing table lists the embryos, the bodies above 20% of the largest mass. At 6,000 years their median spacing is 8.3 mutual Hill radii, τ = 0.42 TL, Locked. Kokubo & Ida (1998, 2000) found oligarchs settling about 10 Hill radii apart.

**Reading it on the phase map.** The starting swarm is packed a few Hill radii apart: τ above TL, Shatter. It reorganizes into fewer, larger bodies until the spacing is Locked. By 6,000 years 82% of the mass is Locked. Nothing in the simulator steers toward Locked; the swarm gets there by colliding.

### 3.5 Worked example 2: fifty million years

**Setup:** defaults, run to 520,000 simulator years. At f = 100 this covers about 50 million years of growth by collision.

| Simulator years | Equivalent for collisions | Bodies | Largest (M⊕) | State |
|-----------------|---------------------------|--------|--------------|-------|
| 0               | 0                         | 200    | 0.012        | crowded swarm, mostly Shatter |
| 5,000           | 0.5 Myr                   | 47     | 0.18         | runaway into oligarchic growth |
| 15,000          | 1.5 Myr                   | 32     | 0.30         | oligarchs forming |
| 75,000          | 7.5 Myr                   | 25     | 0.30         | eccentricities start rising |
| 155,000         | 15 Myr                    | 19     | 0.30         | eccentricities 0.02–0.03 |
| 520,000         | 50 Myr                    | 15     | 0.30         | 100% Locked |

**End state.** Fifteen bodies of 0.15 to 0.30 M⊕ remain, with all 2.36 M⊕ of the starting solids accounted for, after 185 mergers, no hit-and-runs, and nothing lost to the Sun or ejected. Every body is Locked. The median embryo spacing is 14.6 Hill radii, τ = 0.24 TL.

**Where this sits in planet formation.** Spacings near 15 Hill radii hold for tens to hundreds of millions of years before orbits cross (Chambers, Wetherill & Boss 1996). Once they cross, giant impacts merge the oligarchs into two to four planets of Earth and Venus mass over 100 to 200 million years (Chambers 2001). Orbit crossing is set by gravity alone, so for that stage the simulator's clock is not compressed: the run ends at the threshold of the giant-impact stage, with the oligarchs that stage starts from.

### 3.6 Comparisons with observation

- **Mars is a surviving oligarch.** Mars has 0.107 M⊕, and hafnium–tungsten dating shows it reached about half its present size within about 2 million years and never grew into a full planet (Dauphas & Pourmand 2011). The simulator's oligarchs at 0.5 to 1.5 million years carry 0.1 to 0.3 M⊕.
- **The Moon's parent impactor.** The leading account of the Moon's origin is a collision between the growing Earth and a Mars-mass body (Canup & Asphaug 2001). The bodies in the final frame of worked example 2 are that population.
- **Terrestrial-planet spacing.** The Solar System's rocky planets sit 26 to 63 Hill radii apart (Section 5), wider than the oligarchs, as expected after giant impacts merge neighbours.

### 3.7 Applications

- **Teaching.** Runaway growth, oligarchic growth and the isolation mass appear on screen in minutes, with the chart line they are measured against.
- **Parameter studies.** Change Σ₁, the region, the body count or f, export JSON, and compare oligarch masses with M_iso(a).
- **Snow line.** Switch to 0.5–4 AU: beyond 2.7 AU the solids are 4.2 times denser, the isolation mass is about 8.6 times larger, and the outer oligarchs grow visibly heavier.
- **Convergence studies.** Repeat a run with different f or body counts to separate physics from resolution (Section 8).
- **Long-period comet analogue.** In a multi-hour band-mix run, watch for bodies that leave the frame and later return. Their inbound acceleration and perihelion speed spike illustrate why a 30–40 kyr comet looks interstellar until a full orbit is observed.

## 4. Collisions

### 4.1 The criterion

When two bodies touch, their impact speed is v_imp = √(v_∞² + v_esc²), where v_∞ is their approach speed from far away and v_esc = √(2G(M₁ + M₂)/(R₁ + R₂)) is the mutual escape speed. Kokubo and Genda (2010) ran collision simulations across mass ratios and impact angles and found that bodies merge when v_imp is below

v_cr / v_esc = 2.43Γ²Θ^(5/2) − 0.0408Γ + 1.86Θ^(5/2) + 1.08,

with Γ = (M₁ − M₂)/(M₁ + M₂) and Θ = 1 − sin θ for impact angle θ. Above v_cr the smaller body glances off: a hit-and-run (Asphaug 2010). The criterion is the one used for realistic accretion in the giant-impact literature; disruptive collisions (Leinhardt & Stewart 2012) need speeds well above the dispersions in this disk and are listed in the roadmap.

### 4.2 Boundary identification

The collision torsion is

τ_c = TL × v_imp / v_cr,

so a collision merges below TL and hits and runs at or above it (T18). The Impacts chart bins every collision by τ_c/TL with the boundary drawn as a dashed line.

### 4.3 Worked example 3: gentle impacts always merge

Two bodies falling together from rest meet at exactly the escape speed, v_imp = v_esc. The critical speed ranges from 2.94 v_esc for equal masses head-on to 1.08 v_esc for equal masses grazing (T16), and is above v_esc for every mass ratio and angle (T17). A gentle impact therefore always has

τ_c = TL × v_esc / v_cr < TL,

and merges (T20). In the default disk the swarm moves slowly relative to itself, so nearly every collision is gentle: worked example 2 records 185 mergers and no hit-and-runs, and the Impacts chart fills only to the left of the TL line.

### 4.4 Worked example 4: Jupiter stirs the swarm

**Setup:** 0.5–4 AU, JUPITER AT 5.2 AU, Hill-spacing τ.

(Jupiter raises eccentricities and impact speeds in the outer disk, increasing the hit-and-run fraction and opening a partial gap. The outer oligarchs grow more slowly and the Hill spacing table shows wider separations near 5 AU.)

## 5. The Solar System, measured

### 5.1 Hill spacing of the planets

The Solar System preset places the eight planets on their measured orbits (masses, semi-major axes, eccentricities and inclinations from the NASA Planetary Fact Sheet) with random orbital phases and a barycentric start. τ for each neighbouring pair is TL × 2√3 / Δ, Δ in mutual Hill radii.

| Pair            | Δ (R_H) | τ / TL | Phase  |
|-----------------|---------|--------|--------|
| Mercury–Venus   | 26.3    | 0.132  | Locked |
| Venus–Earth     | 26.3    | 0.132  | Locked |
| Earth–Mars      | 40.1    | 0.086  | Locked |
| Mars–Jupiter    | 16.0    | 0.216  | Locked |
| Jupiter–Saturn  | 7.9     | 0.439  | Locked |
| Saturn–Uranus   | 14.0    | 0.247  | Locked |
| Uranus–Neptune  | 14.0    | 0.248  | Locked |

Every pair is Locked (T10). Jupiter–Saturn sits between 0.43 and 0.44 TL (T9), and every other pair sits below TL/4 (T8). The live integration returns the same values: Jupiter–Saturn reads 7.93 Hill radii, τ = 0.437 TL.

**The tightest pair.** Jupiter and Saturn are close to a 5:2 period ratio. Their spacing is the smallest in the system yet still safely Locked.

### 5.2 Applications

- **Exoplanet systems.** Enter the masses and orbits of a multi-planet system into the hill_upper and hill_lower bounds of [9,9,3,25] to place every pair.
- **Stability ranking.** The Hill τ of each pair orders the pairs from most to least secure.

## 6. The Roche Limit and Saturn

### 6.1 Worked example 6: Saturn's rings and moons

Inside the Roche limit, the tidal pull of a planet across a loose body exceeds the body's own gravity, and the body cannot hold together. For a fluid body of density ρ_m around a planet of radius R and density ρ_P,

d_R = 2.44 R (ρ_P / ρ_m)^(1/3).

For water ice around Saturn, d_R lies between 133,393 and 133,422 km (T11). With τ = TL × d_R / d:

| Object                  | Distance (km) | τ / TL | Phase     |
|-------------------------|---------------|--------|-----------|
| D ring, inner edge      | 66,900        | 1.994  | Shatter   |
| C ring, inner edge      | 74,658        | 1.787  | Shatter   |
| B ring, inner edge      | 92,000        | 1.450  | Shatter   |
| B ring, outer edge      | 117,580       | 1.135  | Shatter   |
| A ring, inner edge      | 122,170       | 1.092  | Shatter   |
| Pan                     | 133,584       | 0.999  | IVA Peak  |
| Daphnis                 | 136,505       | 0.977  | IVA Peak  |
| A ring, outer edge      | 136,775       | 0.975  | IVA Peak  |
| Atlas                   | 137,670       | 0.969  | IVA Peak  |
| Prometheus              | 139,380       | 0.957  | IVA Peak  |
| F ring                  | 140,180       | 0.952  | IVA Peak  |
| Pandora                 | 141,720       | 0.941  | IVA Peak  |
| Epimetheus              | 151,410       | 0.881  | IVA Peak  |
| Janus                   | 151,460       | 0.881  | IVA Peak  |
| Mimas                   | 185,539       | 0.719  | Locked    |
| Enceladus               | 238,042       | 0.561  | Locked    |
| Titan                   | 1,221,870     | 0.109  | Locked    |

Every placement is proved in Lean (T15).

**Reading it.** The main rings sit past TL: material that never gathered into a moon, the Shatter state of a moon. The corridor between d_R and d_R/0.88 holds the outer A ring, the F ring and every small moon that lives among the rings: Pan and Daphnis inside gaps in the A ring, Atlas at its edge, Prometheus and Pandora shepherding the F ring, and Janus and Epimetheus at the corridor floor. Moons this close survive by their own rigidity rather than by gravity alone, the IVA condition of holding together under load near the limit. From Mimas outward the moons are Locked.

**Sensitivity.** Janus and Epimetheus sit 0.1% above the IVA floor at an ice density of 0.92 g/cm³. A lower assumed density moves d_R inward and moves them into Locked; the rings and the other ring moons keep their phases across the usual range of ice densities.

### 6.2 Comparisons with observation

Cassini imaging shows the A ring's outer edge, the Encke and Keeler gaps held open by Pan and Daphnis, and the narrow F ring between Prometheus and Pandora (Cuzzi et al. 2010). The phase map marks that whole zone as one corridor.

### 6.3 Applications

- **Ring systems.** Apply the same rule to the rings of Jupiter, Uranus and Neptune with each planet's radius and density.
- **Teaching tides.** The table turns the Roche limit into a single line with three bands that students can check against Cassini images.

## 7. Band Mix and the GAM Collider

### 7.1 What changes

In the BAND MIX · GAM COLLIDER τ model, each planetesimal is born with its own P, N, B and A from the generator's phase bands, as in AxiomForge™ and Galaxy™. Collisions are still decided by the Kokubo–Genda criterion, and each merger combines the two identities by the GAM Collider 2-beam rule. A body whose τ reaches TL reorganizes: it splits into two halves with Pattern 2P, Narrative N/2 and the same Behavior, so each half carries τ/2 (T23), and splitting repeats until every piece sits below TL (T24). Mass and momentum are conserved.

### 7.2 Worked example 7: reorganization slows growth

**Setup:** defaults with BAND MIX · GAM COLLIDER, band mix 25 / 45 / 15 / 15 (Noble / Locked / IVA / Shatter).

At 1,500 simulator years the run records 1,346 mergers and 1,349 fragments, and the largest body carries 0.047 M⊕, against 0.106 M⊕ at 1,000 years in the Hill-spacing model. Two rules produce this:

- **Mergers often cross TL.** The merged Pattern P₁P₂/(P₁ + P₂) is smaller than either parent, so a merger of two bodies with different Behavior frequently lands at τ ≥ TL and reorganizes.
- **Sibling halves remerge to Noble.** Two halves of one body share the same Behavior. When they meet again they merge to B = |B − B| = 0 with the parent's Pattern restored (T25).

The Noble share of bodies grows through the run as sibling pairs remerge. Under the GAM Collider rule a swarm grows by repeated merging and reorganization, and growth proceeds more slowly than under gravity alone.

### 7.3 Emergent long-period returns

In long band-mix runs the merge/fragment cycle continually scatters a few bodies onto high-eccentricity orbits. Most remain in the disk or are removed; a sparse population survives on bound ellipses with aphelia of tens to thousands of AU. These objects spend most of their period far outside the normal view, appear as slow distant points, then return with a sharp perihelion speed spike. Periods reach tens of thousands of years (Kepler’s third law, P = a^{3/2}). From a short observational baseline they look unbound; the simulator shows the return. The effect is not scripted—it appears once the fragment cycle has run long enough to populate the high-e tail.

One recorded session (N = 500, f = 200, band mix) reached 63,000 simulator years with ~201,000 merges and ~201,000 fragments still balanced, largest mass only 0.047 M⊕, and a handful of bodies with aphelia > 50 AU (one at ~2,087 AU, period ~34 kyr). A shorter N = 200, f = 100 run at 2,200 years already showed the largest body at the isolation mass while the fragment cycle remained active and eccentricities stayed low, indicating that the long-period population requires extended churn.

## 8. Verification

| Check                        | Result |
|-----------------------------|--------|
| Mass conservation           | 2.36 M⊕ before and after 185 mergers (worked example 2) |
| Kepler timing               | G = 4π² AU³/(M☉ yr²) gives one orbit at 1 AU in 1.000 year |
| Solar System Hill spacing   | Live integration matches the fact-sheet values; Jupiter–Saturn 7.93 Hill radii |
| Isolation mass at 1 AU      | Simulator 0.097 M⊕; Lean bound 0.096–0.0975 M⊕ (T21) |
| Oligarch spacing            | 8.3 Hill radii at 6,000 years; Kokubo & Ida: about 10 |
| Kokubo–Genda endpoints      | 2.94 v_esc head-on, 1.08 v_esc grazing, equal masses (T16) |
| Seed spread                 | Five independent runs to 6,000 years: 38–43 bodies, largest 0.14–0.24 M⊕, median embryo spacing 8.1–8.9 Hill radii |
| Radius-enhancement convergence | Equal f × time (600,000): f = 50 gives 45 bodies, largest 0.14 M⊕, spacing 8.5; f = 100 gives 38–43, 0.14–0.24, 8.1–8.9; f = 200 gives 48, 0.18, 8.6. Growth scales with f during the collision stages |
| Energy conservation         | Solar System preset over 1,000 years: largest relative energy error 2.2 × 10⁻⁶ |
| Formal proofs               | SNSFL_GC_Accretion_Boundaries_TL [9,9,3,25]: 26 numbered results, 0 sorry |

## 9. Scope

| Part       | Set by the simulator                                      | Produced by the run                          |
|------------|-----------------------------------------------------------|----------------------------------------------|
| Disk       | Minimum Mass Solar Nebula surface density, snow line, equal starting masses, starting eccentricities and inclinations | Runaway and oligarchic growth, oligarch masses and spacing |
| Gravity    | Newton's G, full N-body sum, leapfrog step 0.006 yr      | Orbits, stirring, resonances                 |
| Collisions | Kokubo–Genda criterion, radius enhancement f             | Mergers, hit-and-runs, τ_c distribution      |
| Hill τ     | Gladman boundary 2√3 ↔ TL                                | Phase of every body and pair                 |
| Roche τ    | Fluid Roche limit for ice ↔ TL                           | Phase of every ring and moon                 |
| Band mix   | PNBA at birth, GAM Collider 2-beam rule, reorganization by halves | Growth under identity rules; long-term fragment cycle and sparse high-e returns |

The simulator follows solids only. Nebular gas, gas drag and the capture of gas envelopes by giant planets are outside it, so it forms rocky and icy bodies, not gas giants. Collisions either merge or hit and run; fragmenting collisions are on the roadmap. The radius-enhancement factor compresses the collision stages by about f and leaves orbit-crossing timescales unchanged (Section 3.3). High-eccentricity scattering appears as an emergent product of long band-mix runs; it is a visual analogue for long-period comets, not a controlled comet model.

## 10. Relation to the Other Simulators

| Simulator                        | Substrate                  | Boundary                                                                 |
|----------------------------------|----------------------------|--------------------------------------------------------------------------|
| String-Breaking Simulator™ [9,9,3,22] | Gauge string on a trapped-ion chain | The string breaks at τ = TL into two Noble pairs                        |
| Electron Geometry Simulator™ [9,9,3,21] | Hydrogen atom             | The bound pair shatters at τ = TL into a free electron and a proton     |
| Galaxy™ [9,9,3,24]              | Galactic disk              | Toomre Q = 1 identified with τ = TL; unstable rings clump               |
| Accretion Simulator™ [9,9,3,25] | Planetesimal disk and Solar System | Hill spacing 2√3, Roche limit d_R and critical impact speed v_cr, each identified with τ = TL |

The same boundary governs all four, from a hydrogen atom to a galactic disk. The Accretion Simulator™ adds three boundaries from one domain, each read by the same rule, and the String-Breaking Simulator's picture of one identity breaking into smaller stable ones appears here as rings inside the Roche limit and as the fragment-cycle reorganization in band-mix runs.

## 11. Roadmap

- **Fragmenting collisions.** The Leinhardt & Stewart (2012) regimes for erosive and disruptive impacts, with fragments placed by τ.
- **Gas.** Nebular gas drag and envelope capture, toward a giant-planet stage beyond the snow line.
- **Exoplanet presets.** Measured multi-planet systems placed by Hill τ.
- **More ring systems.** Jupiter, Uranus and Neptune against their Roche limits.
- **Composition τ.** Starting τ from rock and ice fractions instead of the band mix.
- **High-eccentricity population.** Controlled seeding or longer-term statistics of the returning high-e bodies that emerge from the fragment cycle.

## 12. Summary

The Accretion Simulator™ grows planets from a Minimum Mass Solar Nebula under full Newtonian gravity, resolves every collision by the Kokubo–Genda criterion, and reads three stability boundaries of planetary systems—Hill spacing, the Roche limit and the critical impact speed—with one rule: τ = TL × (critical ÷ measured). The runs reproduce runaway growth, oligarchic growth, the isolation mass at 1 AU and oligarch spacing, and a fifty-million-year run ends at the threshold of the giant-impact stage with every body Locked. On the measured Solar System every neighbouring pair of planets is Locked, with Jupiter–Saturn the tightest; around Saturn the main rings read Shatter, the ring moons fill the IVA corridor, and Mimas outward is Locked. In band-mix mode the GAM Collider reorganization rule produces a persistent fragment cycle that slows net growth and, over long runs, scatters a sparse population of high-eccentricity bodies onto returning orbits with periods of hundreds to tens of thousands of years. The placements are proved in Lean from cited measurements in [9,9,3,25].

## References

- Asphaug, E. (2010). Similar-sized collisions and the diversity of planets. *Chemie der Erde* 70, 199.
- Canup, R. M. & Asphaug, E. (2001). Origin of the Moon in a giant impact near the end of the Earth's formation. *Nature* 412, 708.
- Chambers, J. E. (2001). Making more terrestrial planets. *Icarus* 152, 205.
- Chambers, J. E., Wetherill, G. W. & Boss, A. P. (1996). The stability of multi-planet systems. *Icarus* 119, 261.
- Cuzzi, J. N. et al. (2010). An evolving view of Saturn's dynamic rings. *Science* 327, 1470.
- Dauphas, N. & Pourmand, A. (2011). Hf–W–Th evidence for rapid growth of Mars and its status as a planetary embryo. *Nature* 473, 489.
- Gladman, B. (1993). Dynamics of systems of two close planets. *Icarus* 106, 247.
- Hayashi, C. (1981). Structure of the solar nebula, growth and decay of magnetic fields and effects of magnetic and turbulent viscosities on the nebula. *Progress of Theoretical Physics Supplement* 70, 35.
- Kokubo, E. & Genda, H. (2010). Formation of terrestrial planets from protoplanets under a realistic accretion condition. *The Astrophysical Journal Letters* 714, L21.
- Kokubo, E. & Ida, S. (1996). On runaway growth of planetesimals. *Icarus* 123, 180.
- Kokubo, E. & Ida, S. (1998). Oligarchic growth of protoplanets. *Icarus* 131, 171.
- Kokubo, E. & Ida, S. (2000). Formation of protoplanets from planetesimals in the solar nebula. *Icarus* 143, 15.
- Kokubo, E. & Ida, S. (2002). Formation of protoplanet systems and diversity of planetary systems. *The Astrophysical Journal* 581, 666.
- Leinhardt, Z. M. & Stewart, S. T. (2012). Collisions between gravity-dominated bodies. I. *The Astrophysical Journal* 745, 79.
- Mac Lane, S. (1971). *Categories for the Working Mathematician*. Springer.
- Murray, C. D. & Dermott, S. F. (1999). *Solar System Dynamics*. Cambridge University Press.
- Roche, É. (1849). La figure d'une masse fluide soumise à l'attraction d'un point éloigné. *Mémoires de l'Académie des Sciences de Montpellier* 1, 243.
- Tsiganis, K., Gomes, R., Morbidelli, A. & Levison, H. F. (2005). Origin of the orbital architecture of the giant planets of the Solar System. *Nature* 435, 459.
- Weidenschilling, S. J. (1977). The distribution of mass in the planetary system and solar nebula. *Astrophysics and Space Science* 51, 153.
- Wetherill, G. W. & Stewart, G. R. (1989). Accumulation of a swarm of small planetesimals. *Icarus* 77, 330.
- Williams, D. R. Planetary Fact Sheet. NASA Space Science Data Coordinated Archive.

---

Accretion Simulator™, Galaxy™, AxiomForge™, String-Breaking Simulator™, Electron Geometry Simulator™, Identity Physics™, Applied Identity Physics™, SNSFT™, PNBA™, the Sovereign Anchor Constant™, the Torsion Limit™, the Long Division Protocol™ (LDP™) and HIGHTISTIC™ are common law trademarks of HIGHTISTIC (Russell Vernon Trent III) and the SNSFT Foundation.

© 2026 HIGHTISTIC (Russell Vernon Trent III) / SNSFT Foundation · DOI 10.5281/zenodo.18719748 · uuia.app/accretion
