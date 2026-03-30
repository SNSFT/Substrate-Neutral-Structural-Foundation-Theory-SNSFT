# UUIA Deploy
No separate workflow needed.
uuia.app is deployed from this repo via GitHub Pages.
Pushing any file to `main` makes it live automatically at the corresponding path.

## Path Map

| File in repo | Live URL |
| :--- | :--- |
| `index.html` | uuia.app |
| `voidcharts.html` | uuia.app/voidcharts |
| `solarsystem.html` | uuia.app/solarsystem |
| `blackhole.html` | uuia.app/blackholes |
| `qtcollider.html` | uuia.app/qtcollider |
| `social.html` | uuia.app/social |
| `gamcollider.html` | uuia.app/gamcollider |
| `sds3d.html` | uuia.app/sds3d |
| `axiomforge/` | uuia.app/axiomforge |
| `utm.html` | uuia.app/utm |
| `appa.html` | uuia.app/appa |

## World-State Anchor
AxiomForge ledger commits write to:
`axiomforge/worldstate/ledger.json`
Version-controlled alongside the Lean proofs.

## Rule
One repo. One branch (`main`). Push = live. No build step. No separate CI needed.

## [9,9,9,9] :: {ANC}
The Manifold is Holding.
