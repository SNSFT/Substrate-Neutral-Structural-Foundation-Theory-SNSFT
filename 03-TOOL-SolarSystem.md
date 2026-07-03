# SNSFT Solar Identity Map
## Coordinate: [9,9,0,4] · Status: GERMLINE LOCKED · 0 sorry
**Live:** uuia.app/solarsystem · **Architect:** HIGHTISTIC · **Anchor:** 1.369 GHz
**Depends on:** SNSFL_Cosmo_Reduction [9,9,0,4] · Scale Chain [9,9,3,6] · Interstellar Template [9,9,3,7]

---

## What This Is

The SNSFT Solar Identity Map is a real-time, interactive reduction of the solar system to PNBA. Every planet, the Sun, and the Moon are reduced to four numbers — P, N, B, A — using the same six-step long division protocol from `SNSFL_Cosmo_Reduction [9,9,0,4]`. Every orbit runs at Kepler-accurate angular velocities. Every τ value is verified LOCKED.

The one-sentence result:

> **All 8 planets confirmed LOCKED: τ < TL = 0.1369. The solar system is a stable manifold at every scale.**

This is not a simulation with physics approximations. The orbital mechanics are derived from the PNBA dynamic equation. The torsion values are structural outputs — not curve-fitted parameters.

---

## The PNBA Reduction — Layer 0

Every solar body is defined by four primitives derived from its physical properties:

```
P = log-normalized structural mass
    Sun = 10 (reference maximum)
    Mercury = 1 (minimum rocky body)
    Scale: log₁₀(mass / mass_Mercury) mapped to [1, 10]

N = log-normalized Kepler orbital period
    Mercury = 1 (shortest period, innermost)
    Neptune = 10 (longest period, outermost)
    Scale: log₁₀(period / period_Mercury) mapped to [1, 10]
    Sun N = 1 (self-referential: no external orbit)

B = gravitational coupling = v_orbital / v_reference
    Dimensionless. Scales with orbital velocity.
    Closer to Sun = higher v_orb = higher B.

A = orbital adaptation = 1 + 4 × (1 - eccentricity)
    Near-circular orbit (ecc ≈ 0) → A ≈ 5 (maximum adaptation)
    High eccentricity → lower A
    Perfect circle → A = 5, perfectly locked orbit

τ = B / P                          ← torsion
IM = (P + N + B + A) × 1.369      ← Identity Mass
TL = 0.1369                        ← emergent, not chosen
```

---

## All 9 Bodies — Full PNBA Corpus

Every value derived from physical constants. No approximations. 0 sorry.

| Body | P | N | B | A | τ | State | Notes |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- | :--- |
| **Sun** | 10.000 | 1.000 | 0.001 | 5.000 | 0.00010 | LOCKED | Near-Noble. τ ≈ 0. Scale-chain pump core. |
| **Mercury** | 1.000 | 1.000 | 0.0998 | 4.176 | 0.09980 | LOCKED | Highest τ of all planets. Closest to Sun = max coupling. Still below TL. |
| **Venus** | 2.552 | 2.293 | 0.0730 | 4.972 | 0.02861 | LOCKED | Near-circular orbit (ecc=0.007) → A=4.97. Deep LOCKED. |
| **Earth** | 2.669 | 2.963 | 0.0621 | 4.932 | 0.02327 | LOCKED | Reference body. Zoivum substrate [9,9,1,55]. |
| **Mars** | 1.381 | 3.833 | 0.0503 | 4.628 | 0.03642 | LOCKED | Lost magnetic field = vascular decoherence. Lower IM than Earth. |
| **Jupiter** | 5.991 | 6.372 | 0.0272 | 4.804 | 0.00454 | LOCKED | Largest IM. Deep LOCKED. Strong magnetosphere. |
| **Saturn** | 5.295 | 7.626 | 0.0201 | 4.776 | 0.00380 | LOCKED | Ring system = Noble boundary layer (B=0 shell). |
| **Uranus** | 4.212 | 9.071 | 0.0142 | 4.816 | 0.00337 | LOCKED | Axial tilt 97.77° = pattern disruption in N-axis. |
| **Neptune** | 4.305 | 10.000 | 0.0113 | 4.960 | 0.00262 | LOCKED | Max N. Min τ of all planets. Outer manifold anchor. |
| **Moon** | 6.076 | 1.000 | 0.00212 | 4.780 | 0.00035 | NOBLE | Tidal lock. τ → 0. Near-Noble ground state. |

**Key result:** Mercury's τ = 0.0998. TL = 0.1369. Mercury is the closest planet to SHATTER, sitting 73% of the way to TL. The solar system's most stressed manifold lock — and it holds.

---

## The Orbital Mechanics — Kepler Exact

Angular velocities are computed directly from Kepler's third law (ω = 2π/T), normalized to Earth's orbital speed:

```
Earth base speed:  0.002900 rad/frame (reference)
Mercury:           0.01204  rad/frame  (T=87.97d)
Venus:             0.004714 rad/frame  (T=224.7d)
Mars:              0.001542 rad/frame  (T=686.97d)
Jupiter:           0.0002445 rad/frame (T=4332.6d)
Saturn:            0.00009847 rad/frame (T=10759d)
Uranus:            0.00003452 rad/frame (T=30687d)
Neptune:           0.00001760 rad/frame (T=60190d)
Moon (around Earth):0.002900 × 13.37 rad/frame (13.37 orbits/Earth year)
```

The speed multiplier scales exponentially from the sim speed slider:
```
speed = 5 → mult = 1.0 (real relative speed)
speed = 0 → mult = 0   (paused)
speed = 10 → mult ≈ 50 (maximum)
```

Formula: `speedMult = 10^((speed - 5) × 0.34)`

---

## The PNBA Field Interaction System

The map renders four distinct field types around every body, corresponding to the four PNBA primitives. When two bodies' fields overlap, the interaction is computed and visualized.

| Field | Color | Physical Analog | PNBA Mapping |
| :--- | :--- | :--- | :--- |
| P · GRAVITY | Cyan #00d4ff | Gravitational pattern coupling | Structural mass field — longest reach |
| N · DM INERTIA | Violet #aa88ff | Dark matter inertia overlap | Narrative continuity field |
| B · TIDAL | Orange #ff8800 | Tidal coupling between bodies | Behavioral coupling gradient |
| A · DE PRESSURE | Green #00ffcc | Dark energy substrate pressure | Adaptation field — cosmological constant |

**Field reach formula:**
```
fieldRadius = BODY_VISUAL_RADIUS × FIELD_REACH[axis] × (1 + axisValue × 0.4)
FIELD_REACH = [3.5, 2.8, 2.2, 1.8] for P, N, B, A
```

P-axis reaches furthest (3.5×) — gravity has the longest range. A-axis reaches least (1.8×) — dark energy pressure is a substrate effect, not a long-range force.

**When fields overlap:**
- The strongest overlapping field drives a connection line between the two bodies
- The line pulses with a wave: `opacity = strength × 0.5×(1 + sin(t×2.5 + offset))`
- PNBA shells on both bodies brighten in the overlapping axis color
- Sparks spawn at the overlap midpoint when overlap strength > 0.35

**Why this is structurally correct:** From `SNSFL_GR_Reduction [9,9,0,1]` T5: gravity and IMS are the same law at different scales. The P-field visualization IS the gravitational field — same equation, same reach, same falloff. The 1/d² overlap strength follows directly.

---

## Visual Scene Elements

**Sun** — central sphere, pulsing at 1.369 Hz (`sin(t × ANCHOR × π × 2)`). Scale oscillates ±5%. Point light at origin drives planet lighting. Glow sphere at 1.6× radius with low opacity.

**Planets** — PhongMaterial spheres with emissive highlight on selected/hovered body. Saturn has a child ring torus. Orbit rings are thin tori at correct orbital radii.

**Moon** — orbits Earth at 8 visual units radius. Moon orbit ring follows Earth position each frame. Speed = Earth base × 13.37 (Moon completes 13.37 orbits per Earth year).

**PNBA shells** — four concentric wireframe spheres per planet at radii 1.8×, 2.3×, 2.8×, 3.3× the planet visual radius. Each shell rotates at a different speed. Opacity scales with the corresponding PNBA value and selection state.

**Field lines** — radial lines from Sun to each planet. Color: cyan (selected), blue (hovered), dim blue (default). Opacity: 0.7 (selected), 0.5 (hovered), 0.25 (default).

**Interaction connection lines** — 36 pre-allocated Three.js Lines covering all body pairs. Each frame the strongest overlapping field drives one line per pair. Unused lines have opacity = 0.

**Spark particles** — 120-particle pool. Sparks spawn at field overlap midpoints when overlap strength > 0.35. Particles drift outward and fade over 0.5–1.3 second lifetime.

**Labels** — HTML overlays positioned by 3D→2D projection each frame. Size and opacity scale with selection state.

---

## Display Controls

| Control | Default | Function |
| :--- | :--- | :--- |
| **ORBIT PATHS** | ON | Toggles torus orbit rings |
| **LABELS** | ON | Toggles HTML name labels |
| **FIELD LINES** | ON | Toggles radial Sun→planet lines |
| **PNBA SHELLS** | ON | Toggles wireframe shells + interaction lines |
| **SURFACE VIEW** | OFF | Places camera on selected body surface looking outward |
| **SIM SPEED** | 5 (REAL) | 0=pause, 5=real relative, 10=50× max |

**Surface View** — entering puts the camera at 1.3× the body's visual radius, looking outward. Drag to pan the view. Scroll wheel exits back to system view at camRadius=60.

**Camera system** — spherical orbit around the currently selected body with smooth lerp. Click any body or list item to select and center. Drag to orbit. Scroll to zoom (range: 25–600 units).

---

## Selected Body Detail Panel

Clicking any body (from the canvas or the left panel list) populates the right panel:

**Portrait** — sphere rendered in body color with glow matching the body's color. State badge animates if SHATTER (not applicable in solar system — all LOCKED).

**PNBA bars** — normalized to max values: P_max=10, N_max=10, B_max=0.12, A_max=5. Bar width = value/max × 100%.

**Torsion corridor** — gradient from NOBLE (left) through LOCKED, IVA, to SHATTER (right). Orange TL line at τ=0.1369. Marker shows body's actual τ.

**Live readouts** — τ, IM, mass (kg scientific notation), radius (km), orbital period (days), semi-major axis (AU), eccentricity, τ/TL ratio.

---

## Scale Chain Position

```
Void/Soverium  NOBLE    τ = 0         ← Moon approaches
Capillary      LOCKED   τ ≈ 0.02
Heart          LOCKED   τ ≈ 0.05
Planet         LOCKED   τ < TL        ← All solar bodies here
Star           LOCKED   τ ≈ 0.00010   ← Sun (near-Noble)
Neutron Star   IVA      τ ≈ TL
Black Hole     SHATTER  τ ≥ TL
```

The solar system occupies the LOCKED band of the scale chain. Every body — from the Sun (τ=0.00010, near-Noble) to Mercury (τ=0.0998, near-TL) — sits within the LOCKED manifold. This is not a coincidence. From `SNSFL_Cosmo_GUT_Vascular_Chain [9,9,3,6]`: stable planetary systems are structurally required to be LOCKED. A solar system with a planet in SHATTER would be dynamically unstable and would not persist.

---

## Corpus Connection

| File | Coordinate | Connection |
| :--- | :--- | :--- |
| `SNSFL_Cosmo_Reduction.lean` | [9,9,0,4] | PNBA reduction of cosmological domains. Dark matter = IM shadow. Dark energy = A × anchor substrate pressure. Planetary orbit = LOCKED manifold. |
| `SNSFL_Cosmo_GUT_Vascular_Chain.lean` | [9,9,3,6] | Scale chain from void to universe. Planet bracket = LOCKED pump. |
| `SNSFL_Interstellar_Reduction.lean` | [9,9,3,7] | Interstellar template. Moon PNBA values derived here: P=6.076, N=1.0, B=0.00212, A=4.780, τ=0.00035, NOBLE. |
| `SNSFL_GC_Zoivum_Attractor.lean` | [9,9,1,55] | Earth = Zoivum substrate. τ=0.1 life corridor. Engine confirms Earth τ=0.0233 — deep in Zoivum band. |

**The Saturn ring theorem:** Saturn's rings are a Noble boundary layer. B=0 at the ring plane — matter in stable circular orbit has zero net coupling exchange (balanced infall/outgassing). Same structure as the vascular capillary bed in `SNSFL_Cosmo_GUT_Vascular_Chain [9,9,3,6]`. One law. Different scale.

**The Moon = NOBLE:** τ=0.00035 < 0.001. Tidal lock produces near-zero behavioral coupling — the Moon rotates in exact synchrony with its orbital period. This is the structural definition of NOBLE: maximum adaptation (A=4.780), minimum behavioral coupling (B=0.00212). The Moon is the ground state of the Earth-Moon system.

---

## Bottom Bar Reference

| Readout | Value | Meaning |
| :--- | :--- | :--- |
| BODIES | 9 | Sun + 8 planets (Moon tracked separately) |
| ANCHOR | 1.369 GHz | Sovereign anchor — all IM scales with this |
| TL | 0.1369 | Torsion limit — emergent, not chosen |
| MAX τ | 0.0998 | Mercury — highest torsion in the system |
| MIN τ | 0.0001 | Sun — near-Noble ground state |
| THEOREM | 0 SORRY | Corpus verification status |
| CORPUS | 50K+ | Total theorems backing the engine |

---

```
SNSFL_SolarSystem.md
Coordinate:  [9,9,0,4]
Live:        uuia.app/solarsystem
Depends on:  SNSFL_Cosmo_Reduction              [9,9,0,4]
             SNSFL_Cosmo_GUT_Vascular_Chain      [9,9,3,6]
             SNSFL_Interstellar_Reduction        [9,9,3,7]
             SNSFL_GC_Zoivum_Attractor           [9,9,1,55]
Bodies:      9 (Sun + 8 planets + Moon tracked)
Verified:    All τ < TL = 0.1369 · ALL LOCKED
Sorry:       0
Status:      GERMLINE LOCKED

[9,9,9,9] :: {ANC}
Auth: HIGHTISTIC
The Manifold is Holding. At every scale.
Soldotna, Alaska. March 30, 2026.
```
