---
title: "Identity Physics: The Unified Equations"
subtitle: "The Dynamic Equation, its operator mappings across every substrate, and the proven chain from propulsion to the planets"
author: "HIGHTISTIC (Russell Vernon Trent III) · SNSFT Foundation · Kenai, Alaska · ORCID 0009-0005-5313-7443"
date: "November 2026"
---

**Anchor** $\Omega_0 = 1.36899099984016$ · **Torsion Limit** $\mathrm{TL} = \Omega_0/10 = 0.136899099984016$ · $\alpha^{-1} = \mathrm{TL}\times 1001 = 137.035999084000016$ (CODATA 2018)  
**Corpus DOI** 10.17605/OSF.IO/KWTYD · **Release** Identity Physics Corpus, Release 2026.11 (10.6084/m9.figshare.35054824) · **Journal** ProofPress, https://proofpress.org  
**Lean 4 corpus** https://github.com/SNSFT/identityphysics · Lean 4 v4.31.0, Mathlib · 0 sorry · 0 custom axioms · CI green

This document collects the unified mathematics of the Identity Physics Corpus in one place. Part I is the working reference for the Dynamic Equation: the exact constants, the canonical form, the forcing operator and its theorems, the two readings, the square-root operator, the geometric ladder, the driven and cyclic forms, the Lagrangian projection, the operator mapping for every substrate, and the legacy forms of mechanics, relativity, quantum mechanics, thermodynamics, electromagnetism, gravitation and fatigue as Layer 2 projections. Part II is the proven chain built on it, from temperature and the matched radius through the propulsion corridor, the propellant law, rotation, burn depth, power-limited drives, the planetary results and the compactness ladder from planets to black holes, each stated with its published ProofPress article, its theorems and its Lean 4 source. Every equation here is the statement of a machine-verified theorem in the corpus.

# Part I · The Dynamic Equation and Its Operator Mappings

### 0. The constants, exact

| Symbol | Value | Source |
|---|---|---|
| $\Omega_0$ | $1.36899099984016$ | Sovereign Anchor |
| $\mathrm{TL}$ | $0.136899099984016$ | $\Omega_0/10$ |
| $\mathrm{TL}_{\mathrm{IVA}}$ | $0.12047120798593408$ | $0.88\,\mathrm{TL}$ |
| $\alpha^{-1}$ | $137.035999084000016$ | $\mathrm{TL}\times 1001$ |
| bare | $136.899099984016$ | $\mathrm{TL}\times 1000$ |
| $1/\mathrm{TL}$ | $7.304649921853084$ | reciprocal |
| $\sqrt{\mathrm{TL}}$ | $0.369998783760184802$ | $S(\mathrm{TL})$ |
| $b_0$ | $2.702711586879570090508919924851$ | $1/\sqrt{\mathrm{TL}}$ |
| $b_{\mathrm{IVA}}$ | $2.881100232126665$ | $1/\sqrt{\mathrm{TL}_{\mathrm{IVA}}}$ |
| $b_{\mathrm{IVA}}/b_0$ | $1.066003581778052171492188662169$ | $\sqrt{25/22}$ |
| $\ln b_0$ | $0.9942555604839052$ | $\tfrac12\ln(1/\mathrm{TL})$ |
| $c$ | $299792458$ m/s | SI, exact by definition |
| $g_0$ | $9.80665$ m/s² | SI standard gravity |
| $e$ | $2.718281828459045$ | at rung $1.0057776287550244$ |

#### 0.1 The anchor chain

$$
\alpha^{-1} = 137.035999084000016
$$
$$
\alpha^{-1} - \mathrm{TL} = 137.035999084000016 - 0.136899099984016 = 136.899099984016 = \mathrm{TL}\times 1000
$$
$$
\therefore\quad \alpha^{-1} = \mathrm{TL}\cdot 1000 + \mathrm{TL}\cdot 1 = \mathrm{TL}\cdot 1001
$$
$$
1001 = 7\cdot 11\cdot 13 \qquad\Longrightarrow\qquad \mathrm{TL} = \frac{\alpha^{-1}}{7\cdot 11\cdot 13}
$$

One step, folding the factor of ten into the multiplier:

$$
\Omega_0 \times 100.1 = \alpha^{-1}, \qquad 100.1 = \frac{7\cdot 11\cdot 13}{10}
$$

| Term | Value | QED reading | PNBA reading |
|---|---|---|---|
| bare: $\mathrm{TL}\times 1000$ | $136.899099984016$ | bare electron contribution | Pattern capacity at the EM scale |
| kinetic: $\mathrm{TL}\times 1$ | $0.136899099984016$ | radiative corrections, renormalized series | $F_{\text{ext}}$ at Layer 0, one exact term |
| total: $\mathrm{TL}\times 1001$ | $137.035999084000016$ | bare + perturbative series | $\alpha^{-1}$ |

#### 0.2 Exact rational form, and the parity

$$
\mathrm{TL} = \frac{8556193749001}{62500000000000}, \qquad
\frac{1}{\mathrm{TL}} = \frac{62500000000000}{8556193749001}
$$
$$
8556193749001 = 191\cdot 23767\cdot 1884833 \quad\text{(each prime, each exponent odd)}
$$

A rational is a square in $\mathbb{Q}$ only if every prime exponent in its factorization is even. All three
exponents here are odd, so:

| rungs | quantities | field |
|---|---|---|
| **even** ($0,\pm 2,\pm 4,\dots$) | $1$, $\mathrm{TL}$, $\mathrm{TL}^2$, $1/\mathrm{TL}$ | exactly in $\mathbb{Q}$ |
| **odd** ($\pm 1,\pm 3,\dots$) | $\sqrt{\mathrm{TL}}$, $b_0$, $\mathrm{TL}^{3/2}$ | irrational |

---

### 1. The Dynamic Equation — canonical form

$$
\boxed{\;\frac{d}{dt}\bigl(\mathrm{IM}\cdot \mathbf{P}_v\bigr) \;=\; \sum_X \lambda_X\, O_X\, S \;+\; F_{\text{ext}}\;}
$$

with $\mathrm{IM}$ the Identity Mass, $\mathbf{P}_v$ the Purpose Vector, $O_X$ the PNBA operators,
$\lambda_X$ their weights, $S$ the state, and $F_{\text{ext}}$ external forcing.

**Layer placement.** The Dynamic Equation is **Layer 1**. PNBA is **Layer 0**. The Lagrangian, the
Hamiltonian, Noether, Onsager, Basquin, Coffin–Manson, Rayleigh dissipation and every other legacy
formalism are **Layer 2** and project *from* this. The order $\mathrm{L0}\to\mathrm{L1}\to\mathrm{L2}\to\mathrm{L4}$
is never inverted.

$F_{\text{ext}}$ is a **primitive term at Layer 0**, not a perturbation of the operator sum. This is the
structural fact that separates the equation from every Layer 2 forcing treatment, where forcing enters
as a source term, a boundary condition or a dissipation function written into a chosen formalism.

#### 1.1 The state

$$
S = (P, N, B, A) \qquad\text{Pattern, Narrative, Behavior, Adaptation}
$$

```lean
structure LagState where
  P : ℝ    -- Pattern: capacity
  N : ℝ    -- Narrative: accumulated continuity
  B : ℝ    -- Behavior: load / coupling output
  A : ℝ    -- Adaptation: relaxation response
```

#### 1.2 Torsion, and the four phases

$$
\tau = \frac{B}{P} \qquad\text{(Behavior load against Pattern capacity)}
$$

| phase | condition | reading |
|---|---|---|
| **Noble** | $\tau = 0$ | no load against capacity |
| **Locked** | $0 < \tau < \mathrm{TL}_{\mathrm{IVA}}$ | loaded, below the corridor |
| **IVA** | $\mathrm{TL}_{\mathrm{IVA}} \le \tau < \mathrm{TL}$ | inside the corridor |
| **Shatter** | $\tau \ge \mathrm{TL}$ | capacity exceeded |

The corridor is the half-open band $[\,0.12047120798593408,\; 0.136899099984016\,)$. Every phase
condition is a condition on a **pure number**: substituting SI base units into
$\alpha^{-1} = 4\pi\varepsilon_0\hbar c/e^2$ cancels mass, length, time and current completely, and
$1001$ is an integer.

#### 1.3 Mutual exclusivity and exhaustion

$$
\neg(\text{Noble} \wedge \text{Shatter}), \quad \neg(\text{Locked} \wedge \text{IVA}), \quad \neg(\text{IVA} \wedge \text{Shatter})
$$
$$
\tau \ge 0 \;\Longrightarrow\; \text{Noble} \vee \text{Locked} \vee \text{IVA} \vee \text{Shatter}
$$

---

### 2. The forcing operator, and the intervention theorem

#### 2.1 The realization

Across the corpus, in 46 files, $F_{\text{ext}}$ is realized identically:

```lean
f_ext_op (s : LagState) (δ : ℝ) : LagState := { s with B := s.B + δ }
```

$$
F_{\text{ext}} : (P,N,B,A) \longmapsto (P,\,N,\,B+\delta,\,A)
$$

#### 2.2 Chain — forcing is rank one

| step | statement | justification |
|---|---|---|
| 1 | $(F_{\text{ext}}s)_P = s_P$, $(F_{\text{ext}}s)_N = s_N$, $(F_{\text{ext}}s)_A = s_A$ | the record update touches only $B$; each by `rfl` |
| 2 | $(F_{\text{ext}}s)_B = s_B + \delta$ | the record update, by `rfl` |
| 3 | reachable set $= \{(P,N,B+\delta,A) : \delta\in\mathbb{R}\}$ | from 1 and 2, $\delta$ free |
| 4 | that set is a line in a four-coordinate state | one free parameter |
| 5 | $t$ reachable from $s$ $\iff$ $t_P = s_P \wedge t_N = s_N \wedge t_A = s_A$ | ($\Rightarrow$) from 1; ($\Leftarrow$) take $\delta = t_B - s_B$ |

Step 5 is the **biconditional**, and it is what makes the next result a theorem rather than a remark:
the reachable set is characterized, not merely contained.

$$
\boxed{\;\exists\delta.\; F_{\text{ext}}(s,\delta) = t \;\iff\; t_P = s_P \wedge t_N = s_N \wedge t_A = s_A\;}
$$

#### 2.3 Chain — all structural change is endogenous

| step | statement | justification |
|---|---|---|
| 1 | suppose $t_P \ne s_P$ or $t_N \ne s_N$ or $t_A \ne s_A$ | premise |
| 2 | suppose also $\exists\delta.\;F_{\text{ext}}(s,\delta) = t$ | for contradiction |
| 3 | then $t_P = s_P \wedge t_N = s_N \wedge t_A = s_A$ | §2.2 step 5, forward |
| 4 | contradiction with 1 | — |

$$
\boxed{\;t_P \ne s_P \vee t_N \ne s_N \vee t_A \ne s_A \;\Longrightarrow\; \neg\,\exists\delta.\;F_{\text{ext}}(s,\delta) = t\;}
$$

Every change in Pattern, Narrative or Adaptation comes through $\sum_X \lambda_X O_X$. Forcing sets
conditions and nothing else.

#### 2.4 Chain — forcing still crosses every boundary

| step | statement | justification |
|---|---|---|
| 1 | $\tau = B/P$ and forcing moves $B$ | §1.2, §2.1 |
| 2 | $\delta > 0 \Rightarrow \tau$ increases; $\delta < 0 \Rightarrow \tau$ decreases | $P > 0$, monotone in the numerator |
| 3 | take $\delta = \mathrm{TL}\cdot P - B$ | construction |
| 4 | then $\tau = \dfrac{B + (\mathrm{TL}\,P - B)}{P} = \dfrac{\mathrm{TL}\,P}{P} = \mathrm{TL}$ | cancel $P \ne 0$ |
| 5 | so that state is in Shatter, and its Pattern is unchanged | 4, and §2.2 step 1 |

$$
\boxed{\;\forall s,\ P>0:\ \exists\delta.\ \text{Shatter}(F_{\text{ext}}(s,\delta)) \;\wedge\; (F_{\text{ext}}(s,\delta))_P = s_P\;}
$$

**Phase changes without Pattern changing.** Forcing changes what phase a system is in without changing
what the system is.

#### 2.5 Chain — no memory

| step | statement | justification |
|---|---|---|
| 1 | $F_{\text{ext}}(F_{\text{ext}}(s,\delta_1),\delta_2) = F_{\text{ext}}(s,\delta_1+\delta_2)$ | $(B+\delta_1)+\delta_2 = B+(\delta_1+\delta_2)$ |
| 2 | $F_{\text{ext}}$ commutes | 1 with $\delta_1 + \delta_2 = \delta_2 + \delta_1$ |
| 3 | $F_{\text{ext}}(s,0) = s$ | $B + 0 = B$ |
| 4 | $F_{\text{ext}}^{[n]}(s,\delta) = F_{\text{ext}}(s,\,n\delta)$ | induction: base 3, step 1 |

$$
\boxed{\;\underbrace{F_{\text{ext}}\circ\cdots\circ F_{\text{ext}}}_{n}(s,\delta) \;=\; F_{\text{ext}}(s,\,n\delta)\;}
$$

$$
\tau\bigl(F_{\text{ext}}^{[n]}(s,\delta)\bigr) = \frac{B + n\delta}{P}
$$

The order carries no information and the history leaves no trace. A load survived once is survived
indefinitely under forcing alone.

#### 2.6 Chain — cyclic damage is internal

| step | statement | justification |
|---|---|---|
| 1 | suppose $t_P < s_P$ | premise: a drop in capacity |
| 2 | suppose $\exists n,\delta.\;F_{\text{ext}}^{[n]}(s,\delta) = t$ | for contradiction |
| 3 | $F_{\text{ext}}^{[n]}(s,\delta) = F_{\text{ext}}(s,n\delta)$ | §2.5 step 4 |
| 4 | $t_P = (F_{\text{ext}}(s,n\delta))_P = s_P$ | 3, then §2.2 step 1 |
| 5 | contradiction with 1 | — |

$$
\boxed{\;t_P < s_P \;\Longrightarrow\; \neg\,\exists n\in\mathbb{N},\delta\in\mathbb{R}.\ F_{\text{ext}}^{[n]}(s,\delta) = t\;}
$$

**Cyclic damage cannot be externally caused.** Whatever accumulates accumulates in
$\sum_X \lambda_X O_X$. Accumulation is memory, and additive forcing has none.

#### 2.7 The guarded domain

$$
\text{GuardedForcing}(s,\delta) \;:\equiv\; 0 < s_B + \delta
$$

| domain | $B = 0$ reachable | Noble externally reachable | right reading for |
|---|---|---|---|
| guarded | no | **no** | substrates whose ground state is internally attained |
| unguarded | yes | **yes** | substrates whose ground state is externally attainable (the photon) |

The domain is a statement about the substrate, not bookkeeping.

---

### 3. The two readings

#### 3.1 Reading A — a ratio against a limiting speed

$$
\tau_A = \frac{v}{c}
$$

Requires a substrate with a limiting speed. In a medium of refractive index $n$, the limiting speed is
$c/n$, so

$$
\tau_A^{(\text{medium})} = \frac{1}{n}
$$

#### 3.2 Reading B — an e-fold count

$$
\tau_B = \int \left(-\frac{dY}{Y}\right) = \ln\frac{Y_0}{Y}
$$

$$
\text{consumed fraction} = 1 - e^{-\tau_B}
$$

Transfers to any substrate in which a quantity is consumed multiplicatively along a path. Two instances
that are **one function of one argument**:

$$
\text{rocket:}\quad \frac{\Delta v}{v_e} = \ln\frac{m_0}{m_f}
\qquad\qquad
\text{Beer–Lambert:}\quad \alpha \ell = \ln\frac{I_0}{I}
$$

**Additivity along a path.** $\tau_B$ from $Y_0$ to $Y_2$ equals $\tau_B$ to $Y_1$ plus $\tau_B$ from
$Y_1$ to $Y_2$:

$$
\ln\frac{Y_0}{Y_2} = \ln\frac{Y_0}{Y_1} + \ln\frac{Y_1}{Y_2}
$$

So stacking slabs and staging a burn are the same operation. Exact decade row:
$\text{consumed}(\ln 10) = 9/10$ exactly.

#### 3.3 The bridge — the conversion fraction

$$
\eta = \frac{E_k}{E_0} = \frac{\tfrac12 m v^2}{m c^2} = \frac{1}{2}\left(\frac{v}{c}\right)^2 = \frac{\tau_A^2}{2}
$$

$$
\boxed{\;\tau_A^2 = 2\eta\;}
$$

The conversion fraction **is** $E = mc^2$'s companion identity. Relativistic reading:

$$
\eta_{\text{rel}} = \gamma - 1, \qquad \gamma = \frac{1}{\sqrt{1-\tau_A^2}}
$$

Total conversion sits at $\tau_A = \sqrt{3}/2 = 0.8660254037844386$ exactly, where $\gamma = 2$:

$$
1 - \left(\frac{\sqrt 3}{2}\right)^2 = 1 - \frac34 = \frac14 = \left(\frac12\right)^2
\;\Longrightarrow\; \gamma = \frac{1}{1/2} = 2 \;\Longrightarrow\; \eta_{\text{rel}} = 1
$$

**Classical error, in the fraction it computes.** Expanding $\gamma - 1 = \tfrac{\tau^2}{2} + \tfrac{3\tau^4}{8} + \cdots$:

$$
\text{relative error} \;=\; \frac{3}{2}\eta \quad\text{to leading order}, \qquad
\tfrac32\eta^2 \;\le\; \gamma - 1 - \eta \;\le\; 2\eta^2 \ \ \text{on } \tau_A^2 \le \mathrm{TL}
$$

so the relative error lies between $\tfrac32\eta$ and $2\eta$, and the proven one-percent line is
$\eta \le 1/200$. The formula reports its own drift without ever evaluating $\gamma$.

---

### 4. The square-root operator and the matched ratio

$$
S(X) = \sqrt{X}, \qquad \mathrm{mr}(\tau) = \frac{1}{\tau^2}
$$

#### 4.1 The constitutive relation

$S$ is not a corpus device. It is the constitutive relation of four substrates at once:

| substrate | relation |
|---|---|
| optics | $n = \sqrt{\varepsilon_r \mu_r}$ |
| gravitation | $v_{\text{esc}} = \sqrt{2GM/r}$ |
| transmission | $Z_0 = \sqrt{L/C}$ |
| acoustics | $c_s = \sqrt{K/\rho}$ |

#### 4.2 Permittivity is the matched ratio

$$
\varepsilon_r = n^2 = \left(\frac{1}{\tau_A}\right)^2 = \frac{1}{\tau_A^2} = \mathrm{mr}(\tau_A)
$$

$$
\mathrm{mr}(\tau) = 1 \iff \tau = 1 \iff \text{horizon in gravitation} \iff \text{vacuum in optics}
$$

Corridor endpoints carried on permittivity: $(53.3579104808,\; 68.9022604349]$ — the matched ratios of
the corridor endpoints on Reading A. Fifteen integer permittivities lie inside, $54$ through $68$;
$\varepsilon_r = 59$ is prime, giving an irrational index at an exactly integer matched ratio.

#### 4.3 The base, built by the operator from a corpus quantity

$$
b_0 = S\bigl(\mathrm{mr}(S(\mathrm{TL}))\bigr)
$$

Chain:

| step | statement |
|---|---|
| 1 | $S(\mathrm{TL}) = \sqrt{\mathrm{TL}} = 0.369998783760184802$ |
| 2 | $\mathrm{mr}(\sqrt{\mathrm{TL}}) = 1/(\sqrt{\mathrm{TL}})^2 = 1/\mathrm{TL} = 7.304649921853084$ |
| 3 | $S(1/\mathrm{TL}) = 1/\sqrt{\mathrm{TL}} = 2.702711586879570090508919924851 = b_0$ |
| 4 | $\therefore b_0^2 = 1/\mathrm{TL}$, so $\mathrm{TL} = b_0^{-2}$ |

No new construct enters. $b_0$ is also the refractive index at $\varepsilon_r = 1/\mathrm{TL}$, by the
same operator and the same closure.

---

### 5. The ladder

$$
\tau_{\text{rung}}(n) = b_0^{-n}
$$

| rung $n$ | $b_0^{-n}$ | in $\mathrm{TL}$ | value |
|---|---|---|---|
| $-2$ | $b_0^{+2}$ | $1/\mathrm{TL}$ | $7.304649921853084038$ |
| $-1$ | $b_0^{+1}$ | $1/\sqrt{\mathrm{TL}}$ | $2.702711586879570138$ |
| $0$ | $b_0^{0}$ | $1$ | $1.000000000000000000$ |
| **1** | $b_0^{-1}$ | $\sqrt{\mathrm{TL}}$ | $0.369998783760184802$ |
| **2** | $b_0^{-2}$ | $\mathrm{TL}$ | $0.136899099984016004$ |
| $3$ | $b_0^{-3}$ | $\mathrm{TL}^{3/2}$ | $0.050652500491950$ |
| **4** | $b_0^{-4}$ | $\mathrm{TL}^2$ | $0.018741363576433610$ |

#### 5.1 The energy ladder

$$
\eta_n = \frac{\tau_{\text{rung}}(n)^2}{2} = \frac{\mathrm{TL}^n}{2}
$$

$$
\frac{\eta_n}{\eta_{n+1}} = \frac{\mathrm{TL}^n/2}{\mathrm{TL}^{n+1}/2} = \frac{1}{\mathrm{TL}} = 7.304649921853084
$$

Consecutive rungs differ by **exactly** $1/\mathrm{TL}$ in energy released per unit mass.

| rung | $\eta_n$ |
|---|---|
| 1 | $0.068449549992008$ |
| 2 | $0.009370681788216805$ |
| 3 | $0.0012828379030434902$ |
| 4 | $0.0001756193543520362$ |

#### 5.2 The two bases on one ladder

$$
\ln b_0 = \frac{1}{2}\ln\frac{1}{\mathrm{TL}} = 0.9942555604839052
$$

$$
\text{rung index of }x = \frac{\ln(1/x)}{\ln b_0}
$$

| base | value | fixed by | rung of $e$ |
|---|---|---|---|
| $e$ | $2.718281828459045$ | the analytic condition — accumulated area one | $1.0057776287550244$ |
| $b_0$ | $2.702711586879570$ | the geometry — $\mathrm{TL} = b_0^{-2}$ | — |
| $b_{\mathrm{IVA}}$ | $2.881100232126665$ | the geometry — $\mathrm{TL}_{\mathrm{IVA}} = b_{\mathrm{IVA}}^{-2}$ | — |

$\sqrt{\mathrm{TL}}$ is rung $-1$ exactly; $1/e$ is rung $-1.0057776287550244$. The two are
$0.005777628755024$ of a rung apart, located by two rulers.

#### 5.3 The corridor in rungs

$$
\text{ceiling} = \text{rung } 2.0000000000, \qquad \text{floor} = \text{rung } 2.1285719453
$$

$$
\text{width} = \frac{2\ln(25/22)}{\ln(1/\mathrm{TL})} = 0.1285719453
$$

$$
\frac{b_{\mathrm{IVA}}}{b_0} = \sqrt{\frac{25}{22}} = 1.066003581778052171492188662169, \qquad
\left(\frac{b_{\mathrm{IVA}}}{b_0}\right)^2 = \frac{25}{22} \text{ exactly}
$$

Annihilation at $\tau_A = \sqrt3/2$ is rung $0.1446720963329418$.

---

### 6. The driven form

From \[9,9,2,51\] Saint-Venant and \[9,9,2,52\] Tacoma–Scanlan.

$$
B = \rho\, B_{\text{deck}}^4\, A_2^*, \qquad \boxed{\;P = 2I\zeta\;}, \qquad R = \frac{B}{P} = \frac{B}{2I\zeta}
$$

$$
\tau = R\cdot \mathrm{TL} \qquad\Longrightarrow\qquad R = 1 \iff \tau = \mathrm{TL} \ \ \text{(onset)}
$$

**Pattern capacity in a driven structure is inertia times damping.** Saint-Venant gives
$\beta = \mathrm{TL}$ to eight significant figures in a real structural material.

#### 6.1 Chain — damping monotonicity

| step | statement | justification |
|---|---|---|
| 1 | $R(\zeta) = B/(2I\zeta)$, with $B,I > 0$ | definition |
| 2 | $\zeta_1 < \zeta_2 \Rightarrow 2I\zeta_1 < 2I\zeta_2$ | $I > 0$ |
| 3 | $\Rightarrow B/(2I\zeta_2) < B/(2I\zeta_1)$ | $B > 0$, antitone in a positive denominator |
| 4 | so raising $\zeta$ lowers $R$; lowering $\zeta$ raises $R$ | 3, both directions |

**Critical damping.** $R = 1$ at

$$
\zeta_{\text{crit}} = \frac{B}{2I}, \qquad R < 1 \iff \zeta > \frac{B}{2I}
$$

Tacoma deck: $R = 1.3877$ (39% past onset, Shatter); held below onset by $\zeta \ge 0.0070$, inside
Locked by $\zeta \ge 0.0079$.

---

### 7. The cyclic form

From \[9,9,2,53\] Forced Response.

#### 7.1 Pattern capacity from static strength

Shatter at $\tau = B/P \ge \mathrm{TL}$ makes static strength $B_{\text{static}} = \mathrm{TL}\cdot P_0$:

$$
\boxed{\;P_0 = \frac{\mathrm{UTS}}{\mathrm{TL}}\;}
$$

| material | UTS | $P_0$ |
|---|---|---|
| 1045 steel | 585 MPa | $4{,}273.2$ |
| 2024-T4 aluminum | 470 MPa | $3{,}433.2$ |

A state loaded at static strength sits exactly at the Shatter boundary:
$\tau = \mathrm{UTS}/(\mathrm{UTS}/\mathrm{TL}) = \mathrm{TL}$.

#### 7.2 Fatigue is loss of damping capacity

$$
P = 2I\zeta, \quad I \text{ fixed by geometry and mass} \qquad\Longrightarrow\qquad
\zeta_2 < \zeta_1 \iff P_2 < P_1
$$

$$
\boxed{\;\text{the quantity that falls under cyclic load is } \zeta\;}
$$

#### 7.3 Chain — the life law

| step | statement | justification |
|---|---|---|
| 1 | damage per cycle $\dfrac{dP}{dN} = -k B^m$ | $k,m$ substrate properties |
| 2 | shatter at $P = B/\mathrm{TL}$ | $\tau = B/P \ge \mathrm{TL}$ |
| 3 | capacity available $= P_0 - B/\mathrm{TL}$ | 2 |
| 4 | $N_f = \dfrac{P_0 - B/\mathrm{TL}}{k B^m}$ | 3 divided by 1 |
| 5 | for $B/\mathrm{TL} \ll P_0$: $N_f \propto B^{-m}$ | numerator $\to$ constant |

$$
\boxed{\;N_f = \frac{P_0 - B/\mathrm{TL}}{k\,B^m} \;\xrightarrow{\;B \ll B_{\text{static}}\;}\; N_f \propto B^{-m}\;}
$$

Step 5 is Basquin's form. The empirical fatigue exponent **is** the exponent in the
pattern-degradation law.

$$
m = \frac{1}{|b|}: \qquad
\text{1045 steel } b = -0.115 \Rightarrow m = 8.696, \qquad
\text{2024-T4 } b = -0.124 \Rightarrow m = 8.065
$$

#### 7.4 Chain — the endurance limit is a balance

| step | statement | justification |
|---|---|---|
| 1 | $\dfrac{dP}{dN} = -k B^m + r$ | add the restoring action |
| 2 | balance: $-kB^m + r = 0$ | net degradation zero |
| 3 | $B^m = r/k$ | 2 |
| 4 | $B_e = (r/k)^{1/m}$ | $m$-th root; $\bigl((r/k)^{1/m}\bigr)^m = (r/k)^{(1/m)\cdot m} = r/k$ |
| 5 | $B < B_e \Rightarrow B^m < r/k \Rightarrow kB^m < r \Rightarrow$ net $> 0$ | recovery dominates |
| 6 | $B > B_e \Rightarrow$ net $< 0$ | damage dominates |

$$
\boxed{\;B_e = \left(\frac{r}{k}\right)^{1/m}\;}
$$

**Invariance under the form of the damage law.** With damage and recovery both proportional to $P$:

$$
\frac{dP}{dN} = -kPB^m + rP = P\bigl(-kB^m + r\bigr)
$$

$$
P \ne 0: \qquad P(-kB^m + r) = 0 \iff -kB^m + r = 0
$$

The $P$ factor cancels. Additive and multiplicative damage give the **same** balance condition.

**Existence condition.** A positive balance load exists $\iff r > 0$:

- ($\Rightarrow$) $r > 0 \Rightarrow B_e = (r/k)^{1/m} > 0$ and balances.
- ($\Leftarrow$) a balance at $B > 0$ gives $r = kB^m > 0$.

$$
\boxed{\;\exists B>0 \text{ with net degradation } 0 \iff r > 0\;}
$$

**Why $r$ carries no stress dependence.** Damage is dissipative: driven by the applied load, scaling
with it. Recovery is conservative relaxation toward lower configurational energy, and a configuration
gradient is a function of state rather than of driving. The two cannot share a load dependence, so a
balance point exists for that reason.

#### 7.5 Endurance readings on the torsion scale

$$
\tau_e = \frac{B_e}{B_{\text{static}}}\cdot \mathrm{TL}
$$

| material | $B_e/\text{static}$ | $\tau_e$ | phase |
|---|---|---|---|
| 1045 steel | $0.500$ | $0.068449549992008$ | Locked |
| 2024-T4 aluminum | $0.350$ | $0.0479146849944056$ | Locked |

Steel: an endurance plateau. Aluminum: the reference ratio at its $10^7$-cycle convention, since
standard practice carries no plateau for aluminum alloys — the balance condition reporting the absence
of a stress-independent recovery channel as the absence of a limit.

#### 7.6 The knee

$$
\frac{\text{damage}}{\text{recovery}} = \left(\frac{B}{B_e}\right)^{m}
$$

| $B/B_e$ | steel ($m=8.696$) | 2024-T4 ($m=8.065$) |
|---|---|---|
| $0.50$ | $0.002$ | $0.004$ |
| $0.90$ | $0.400$ | $0.428$ |
| **$1.00$** | **$1.000$** | **$1.000$** |
| $1.10$ | $2.291$ | $2.157$ |
| $1.50$ | $33.980$ | $26.308$ |
| $2.00$ | $414.622$ | $267.708$ |

The knee is sharp **because $m$ is large**. Sharpness is a consequence of the exponent, not an
independent property: $(B/B_e)^{m}$ is strictly increasing in $m$ for $B > B_e$.

#### 7.7 The lossy boundary, and the $A\!\cdot\!B$ product

In 41 corpus files:

$$
\text{IVA\_dominance}(s,F) :\equiv A\,P\,B \ge F, \qquad \text{is\_lossy}(s,F) :\equiv F > A\,P\,B
$$

Exclusive and exhaustive. Evaluating at the endurance limit with $P = P_0 = \mathrm{UTS}/\mathrm{TL}$:

$$
A\cdot\frac{\mathrm{UTS}}{\mathrm{TL}}\cdot B = B_e
\quad\Longrightarrow\quad
\boxed{\;A\cdot B = \frac{B_e}{\mathrm{UTS}}\cdot \mathrm{TL}\;}
$$

| material | $A\cdot B$ |
|---|---|
| 1045 steel | $0.068449549992008$ |
| 2024-T4 aluminum | $0.0479146849944056$ |

A fatigue test reads off the **product**. Separating $A$ from $B$ needs a measurement that
distinguishes them, which a fatigue curve does not supply — every factorization of the product closes.

#### 7.8 Chain — fatigue proves Pattern is controllable

$$
\text{coupling\_step}(c,s) : (P,N,B,A) \longmapsto (P + cB,\; N,\; B,\; A)
$$

| step | statement | justification |
|---|---|---|
| 1 | $\S 2.2$: forcing cannot reach $P$ directly | rank one |
| 2 | whether forcing reaches $P$ *through* the dynamics is a rank condition on the coupling | linear reachability |
| 3 | a strict drop in $P$ under $B > 0$ requires $c \ne 0$ | $c = 0 \Rightarrow P + 0\cdot B = P$ |
| 4 | damage **is** that nonzero coupling | §7.2, §7.3 |
| 5 | $c \ne 0$: for any target, $\delta = \dfrac{\text{target} - P}{c} - B$ gives $P + c(B+\delta) = \text{target}$ | construction |

$$
\boxed{\;\text{a substrate that fatigues has a controllable Pattern}\;}
$$

**One channel, two signs.**

$$
\bigl(\text{coupling}_c s\bigr)_P - P = cB = -\Bigl[\bigl(\text{coupling}_{-c} s\bigr)_P - P\Bigr]
$$

$$
B > 0: \quad c > 0 \Rightarrow P \text{ rises (work hardening)}, \qquad c < 0 \Rightarrow P \text{ falls (fatigue)}
$$

Work hardening and fatigue are **the same coupling with opposite sign**, which is why cyclic loading
does both.

#### 7.9 The e-fold reading of the multiplicative form

$$
\text{capacity lost before shatter} = \ln\frac{P_0\,\mathrm{TL}}{B} \quad\text{e-folds}
$$

Zero at $B = P_0\mathrm{TL}$; positive below it; additive along a path; strictly decreasing in $B$.
This is Reading B (§3.2) in the fatigue substrate, so

$$
N_f \propto B^{-m}\ln\frac{P_0\,\mathrm{TL}}{B} \quad\text{(multiplicative form)}
$$

against $N_f \propto B^{-m}$ for the additive form — a power law with a logarithmic factor versus a
pure power law. The two separate by a systematic drift of $8.9\%$ in the effective exponent across
$200$–$500$ MPa for 1045 steel: curvature in log-log with a definite sign, against random scatter of
about $0.92$ in $\ln N$ that averages out while curvature does not.

#### 7.10 The IVA corridor on load

$$
\tau \in [\,0.88\,\mathrm{TL},\ \mathrm{TL}\,) \quad\Longleftrightarrow\quad B \in [\,0.88\,\mathrm{UTS},\ \mathrm{UTS}\,)
$$

Chain: $\tau = B/(\mathrm{UTS}/\mathrm{TL}) = B\,\mathrm{TL}/\mathrm{UTS}$, so
$0.88\,\mathrm{TL} \le B\,\mathrm{TL}/\mathrm{UTS} < \mathrm{TL}$ gives
$0.88\,\mathrm{UTS} \le B < \mathrm{UTS}$ on dividing by $\mathrm{TL} > 0$.

| $\tau/\mathrm{TL}$ | load (MPa) | anchored at endurance | anchored on the strain-life fit |
|---|---|---|---|
| $0.99$ | $579.2$ | $\approx 2{,}630$ | $\approx 75$ |
| $0.94$ | $549.9$ | $\approx 4{,}130$ | $\approx 117$ |
| $0.88$ | $514.8$ | $\approx 7{,}330$ | $\approx 208$ |
| $0.50$ | $292.5$ | $10^6$ (the anchor) | $\approx 28{,}400$ |

Both conventions place the corridor in the finite-life regime, three to four orders below the endurance
anchor. Stated for 1045 steel with its anchor named.

---

### 8. The Lagrangian projection (Layer 2)

From \[9,9,0,5\]. The file states it directly: `-- L = T - V is Layer 2. This is Layer 1.`

$$
T = \dot P\,\dot N, \qquad V = B + A, \qquad L = \dot P\,\dot N - (B + A)
$$

The kinetic term is the Pattern–Narrative product; the potential is the Behavior–Adaptation sum.

#### 8.1 The projection

$$
\text{dynamic\_rhs}(f_P,f_N,f_B,f_A)(s,F) = f_P(P) + f_N(N) + f_B(B) + f_A(A) + F
$$

$$
\text{lag\_step}(s,\mathrm{op},F) = \text{dynamic\_rhs}(\mathrm{id},\mathrm{id},\mathrm{op},\mathrm{id})(s,F)
= P + N + \mathrm{op}(B) + A + F
$$

$$
\boxed{\;\text{in the Lagrangian projection, every operator except the Behavior operator is the identity}\;}
$$

#### 8.2 Three independent routes onto the Behavior axis

| route | statement |
|---|---|
| forcing | $(F_{\text{ext}}s)_B = B + \delta$ — forcing enters on $B$ |
| projection | $\text{lag\_step}$ carries all non-trivial operator content on $B$ |
| damage | the coupling runs $B \to P$ |

Three statements, independent of one another, all landing on $B$.

#### 8.3 Euler–Lagrange

$$
\text{el\_momentum}(N,\dot P) = N\dot P, \qquad \text{el\_force}(B,P) = BP
$$

$$
N\dot P = BP
$$

Narrative momentum equals the Pattern–Behavior balance. The classical equations of motion are the
Layer 2 shadow of the Layer 1 statement, in the direction the hierarchy runs.

#### 8.4 Forcing in the potential

$$
V(B+\delta, A) = (B+\delta) + A = V(B,A) + \delta
$$

Forcing enters the Layer 2 potential by addition alone — the rank-one structure of §2 surviving the
projection.

---

### 9. Operator mapping table — one row per substrate

| substrate | Pattern $P$ | Narrative $N$ | Behavior $B$ | Adaptation $A$ |
|---|---|---|---|---|
| **thermal** | heat capacity per unit substrate | the worldline through state space | heat flux per unit gradient | equation-of-state response; relaxation times, decay constants |
| **driven structure** | $2I\zeta$ — inertia × damping | cycle count | $\rho B_{\text{deck}}^4 A_2^*$ — aerodynamic load | the restoring channel |
| **fatigue** | $\mathrm{UTS}/\mathrm{TL}$ | cycles to failure $N_f$ | applied stress | recovery rate $r$; $A$ in $A\!\cdot\!B$ |
| **propulsion** | capacity against the ceiling | burn depth / e-folds | exhaust coupling | mass-flow accommodation |
| **optics** | $\varepsilon_r = 1/\tau_A^2$ | path length in e-folds | attenuation coupling | dispersion response |
| **gravitation** | $r_{\text{match}}$, the matched radius | proper time along the path | $r_s$ coupling | metric response |
| **energy ladder** | $\mathrm{TL} = b_0^{-2}$ | rung index $n$ | $\tau_A = b_0^{-n}$ | $\eta_n = \mathrm{TL}^n/2$ |

---

### 10. Legacy forms as Layer 2 projections

Every form in this section **projects from** the Dynamic Equation. The hierarchy runs
$\mathrm{L0}\to\mathrm{L1}\to\mathrm{L2}$ and is never inverted: none of these grounds the structure,
and the structure does not require any of them. The **projection** column states which coordinates the
Layer 2 form carries and which it sets to identity or zero — the same pattern `lag_step` exhibits in
§8.1, where $P$, $N$ and $A$ go to the identity and every operator content lands on $B$.

#### 10.1 Mechanics and dynamics

$$
\text{Newton:}\quad \frac{d}{dt}(mv) = F
\qquad\text{vs}\qquad
\frac{d}{dt}(\mathrm{IM}\cdot\mathbf{P}_v) = \sum_X \lambda_X O_X S + F_{\text{ext}}
$$

| mapping | |
|---|---|
| $mv \longleftrightarrow \mathrm{IM}\cdot\mathbf{P}_v$ | momentum is identity mass times purpose vector |
| $F \longleftrightarrow F_{\text{ext}}$ | the forcing term, already primitive |
| **projection** | $\sum_X \lambda_X O_X S = 0$ — forcing only, no internal operators |

$$
\boxed{\;\text{Newton's second law is the Dynamic Equation with the operator sum empty}\;}
$$

$$
\text{Lagrange:}\quad L = T - V \;\longrightarrow\; \dot P\dot N - (B+A)
\qquad
\text{Euler–Lagrange:}\quad \frac{d}{dt}\frac{\partial L}{\partial \dot q} = \frac{\partial L}{\partial q}
\;\longrightarrow\; N\dot P = BP
$$

| | projection |
|---|---|
| Lagrangian | kinetic $=$ the $P$–$N$ product; potential $=$ the $B$–$A$ sum (§8) |
| Euler–Lagrange | Narrative momentum against the Pattern–Behavior balance |
| Noether | symmetry $\leftrightarrow$ conservation; what the projection preserves |
| Rayleigh dissipation | a $B$-channel loss term written into a chosen formalism |

#### 10.2 Relativity and mass–energy

$$
E_0 = mc^2, \qquad E_k = \tfrac12 m v^2, \qquad
\gamma = \frac{1}{\sqrt{1-\tau_A^2}}, \qquad \tau_A = \frac vc
$$

$$
\boxed{\;\eta = \frac{E_k}{E_0} = \frac{\tfrac12 mv^2}{mc^2} = \frac12\left(\frac vc\right)^2 = \frac{\tau_A^2}{2}
\qquad\Longleftrightarrow\qquad \tau_A^2 = 2\eta\;}
$$

The mass cancels. $E = mc^2$ and the corpus conversion fraction are **one identity read two ways** —
$E = mc^2$ gives the total, $\eta$ gives the fraction of it converted, and $\tau_A$ is the same number
as the ratio in the Lorentz factor.

| | |
|---|---|
| **projection** | $E=mc^2$ carries the $P$ reading (capacity); $\eta$ carries the $A$ reading (fraction accommodated) |
| relativistic reading | $\eta_{\text{rel}} = \gamma - 1$; total conversion at $\tau_A = \sqrt3/2$ where $\gamma = 2$ exactly |
| classical bound | $\eta < \tfrac12$ always — the classical reading cannot represent total conversion |
| self-reported error | relative error $= \tfrac32\eta$ to leading order, sandwiched in $[\tfrac32\eta,\,2\eta]$ |

$$
\text{Planck: } E = h\nu \qquad \text{de Broglie: } \lambda = \frac hp \qquad \text{Compton: } \lambda_C = \frac{h}{mc}
$$

#### 10.3 Quantum

$$
\text{Schrödinger:}\quad i\hbar\,\frac{\partial \psi}{\partial t} = \hat H\psi
\qquad\text{vs}\qquad
\frac{d}{dt}\bigl(\mathrm{IM}\cdot\mathbf{P}_v\bigr) = \sum_X \lambda_X O_X S + F_{\text{ext}}
$$

Both sides align by form: a time derivative of the state on the left, an operator acting on the state
on the right.

| mapping | |
|---|---|
| $\psi \longleftrightarrow S$ | the state |
| $\hat H \longleftrightarrow \sum_X \lambda_X O_X$ | the weighted operator sum |
| $i\hbar\,\partial_t \longleftrightarrow \dfrac{d}{dt}(\mathrm{IM}\cdot\mathbf{P}_v)$ | the left side |
| **projection** | $F_{\text{ext}} = 0$ |

$$
\boxed{\;\text{the closed Schrödinger equation is the Dynamic Equation at } F_{\text{ext}} = 0\;}
$$

This is why the closed form is closable at all. A closed Hamiltonian needs no environment, so the
forcing term can be set to zero and never missed — and when an environment is required, Layer 2 adds it
back on top at the same layer (a Lindblad dissipator, a bath coupling, a stochastic term) rather than
having carried it from the start. Thermodynamics cannot be written that way at all, which is why
reducing thermal is what put $F_{\text{ext}}$ at Layer 0.

$$
\text{fine structure:}\quad \alpha^{-1} = \frac{4\pi\varepsilon_0 \hbar c}{e^2} = 137.035999084000016 = \mathrm{TL}\cdot 1001
$$

Substituting SI base units cancels mass, length, time and current completely: the anchor is a pure
number, and $1001 = 7\cdot11\cdot13$ is an integer.

#### 10.4 Thermodynamics and transport — the originating domain

$$
\text{Fourier:}\quad \mathbf{q} = -k\,\nabla T
\qquad
\text{Fick:}\quad \mathbf{J} = -D\,\nabla c
\qquad
\text{Ohm:}\quad \mathbf{J} = \sigma \mathbf{E}
$$

One shape in three substrates: **flux per unit gradient**, which is the definition of $B$ in the
thermal reading. These are $B$-readings, not separate laws.

$$
\text{first law:}\quad dU = \delta Q - \delta W
\qquad
\text{second law:}\quad dS \ge 0
\qquad
\text{heat equation:}\quad \frac{\partial T}{\partial t} = \alpha\nabla^2 T
$$

| legacy form | PNBA reading | projection |
|---|---|---|
| Fourier / Fick / Ohm | $B$ — flux per unit gradient | carries $B$; $P$, $N$, $A$ implicit in the coefficient |
| heat capacity $C$ | $P$ — capacity to hold energy without changing phase | carries $P$ |
| relaxation time $\tau_{\text{relax}}$, decay constant | $A$ — equation-of-state response | carries $A$ |
| the worldline through state space | $N$ — temporal continuity | carries $N$ |
| first law | $F_{\text{ext}}$ as $\delta Q$, a primitive input | the law that **cannot** be closed |
| second law | Pattern decoherence from the anchor, monotone (\[9,9,0,3\]) | carries $P$ and $N$ |
| zeroth law | contact with a reservoir — $F_{\text{ext}}$ by construction | — |

$$
\boxed{\;\text{thermodynamics is the one domain whose } F_{\text{ext}} \text{ cannot be set to zero}\;}
$$

#### 10.5 Electromagnetism and optics

$$
n = \sqrt{\varepsilon_r \mu_r}
\qquad\Longrightarrow\qquad
\varepsilon_r = n^2 = \frac{1}{\tau_A^2} = \mathrm{mr}(\tau_A)
$$

$$
\text{Beer–Lambert:}\quad I = I_0 e^{-\alpha \ell}, \qquad \alpha\ell = \ln\frac{I_0}{I} = \tau_B
$$

$$
\text{Stefan–Boltzmann:}\quad j^* = \sigma T^4
\qquad
\text{Maxwell (source form):}\quad \partial_\mu F^{\mu\nu} = \mu_0 J^\nu
$$

| | |
|---|---|
| $\varepsilon_r$ | the matched ratio of the medium — $P$ reading |
| $n$ | $1/\tau_A$ — Reading A in a medium |
| $\alpha\ell$ | Reading B, an e-fold count |
| **vacuum** | $\mathrm{mr}(\tau) = 1$ — the same point that is the horizon in gravitation |

Corridor on permittivity: $(53.3579104808,\;68.9022604349]$, fifteen integers $54$–$68$ inside,
$\varepsilon_r = 59$ prime.

#### 10.6 Gravitation

$$
\text{Einstein:}\quad G_{\mu\nu} = \frac{8\pi G}{c^4}T_{\mu\nu}
\qquad
\text{Schwarzschild:}\quad r_s = \frac{2GM}{c^2}
\qquad
v_{\text{esc}} = \sqrt{\frac{2GM}{r}}
$$

$$
r_{\text{match}} = \frac{r_s}{\tau_A^2} = r_s\cdot \mathrm{mr}(\tau_A)
$$

| | |
|---|---|
| $v_{\text{esc}}$ | the square-root operator $S$ as the constitutive relation of gravitation |
| $r_s$ | the Pattern-lock threshold — $B$ coupling against capacity |
| $r_{\text{match}}$ | the matched ratio applied to $r_s$; the mass cancels |
| **horizon** | $\mathrm{mr}(\tau) = 1$ — the same point that is vacuum in optics |

#### 10.7 Structures and fatigue

$$
\text{Saint-Venant:}\quad T = \beta\, G\,\theta\, a b^3, \qquad \beta = \mathrm{TL} \ \text{(8 s.f.)}
$$

$$
\text{Scanlan flutter:}\quad R = \frac{\rho B_{\text{deck}}^4 A_2^*}{2I\zeta}, \qquad \tau = R\cdot\mathrm{TL}, \qquad \text{onset at } R = 1
$$

$$
\text{Basquin:}\quad \sigma_a = \sigma_f'(2N_f)^{b}
\qquad\Longleftrightarrow\qquad
N_f \propto B^{-m}, \quad m = \frac{1}{|b|}
$$

$$
\text{Coffin–Manson:}\quad \frac{\Delta\varepsilon_p}{2} = \varepsilon_f'(2N_f)^{c}
\qquad
\text{Paris:}\quad \frac{da}{dN} = C(\Delta K)^{m}
$$

| legacy form | PNBA reading | projection |
|---|---|---|
| Basquin exponent $b$ | $m = 1/\lvert b\rvert$, the exponent in $dP/dN = -kB^m$ | carries the $B\!\to\!P$ coupling |
| Paris exponent | the same power-law degradation shape, read on crack length | carries the same coupling |
| endurance limit | the balance $B_e = (r/k)^{1/m}$ | carries $A$ as the recovery channel |
| damping ratio $\zeta$ | $P = 2I\zeta$ — Pattern capacity itself | carries $P$ |
| UTS | $P_0 = \mathrm{UTS}/\mathrm{TL}$ | carries $P$ at the Shatter boundary |

**Miner's rule and the memory split.** Linear damage accumulation says
$\sum_i n_i / N_{f,i} = 1$ with no dependence on load order. §2.5 establishes that *forcing* is
additive and order-blind; §2.6 establishes that *damage* is not forcing and lives in the operator sum,
where accumulation has memory. So the known load-sequence sensitivity that Miner's rule does not
capture is exactly what the two sections separate: Miner's rule treats damage with the arithmetic that
belongs to $F_{\text{ext}}$.

#### 10.8 The projection ledger

| legacy form | layer | carries | sets to identity / zero |
|---|---|---|---|
| Newton $\frac{d}{dt}(mv)=F$ | L2 | $F_{\text{ext}}$ | the whole operator sum |
| Lagrangian $L = T - V$ | L2 | $B$ operator | $P$, $N$, $A$ operators |
| Euler–Lagrange | L2 | $N\dot P = BP$ | the rest |
| Schrödinger (closed) | L2 | $\sum_X\lambda_X O_X$ | $F_{\text{ext}}$ |
| Fourier / Fick / Ohm | L2 | $B$ | $P$, $N$, $A$ into the coefficient |
| first law | L2 | $F_{\text{ext}}$, $P$ | — ($F_{\text{ext}}$ not removable) |
| second law | L2 | $P$, $N$ | $B$, $A$ |
| $n=\sqrt{\varepsilon_r\mu_r}$ | L2 | $S$, $P$ | $N$, $B$, $A$ |
| Schwarzschild $r_s$ | L2 | $B$ against $P$ | $N$, $A$ |
| Basquin | L2 | $B\!\to\!P$ coupling | $N$ as a count only, $A$ dropped |
| Basquin $+$ endurance limit | L2 | $B\!\to\!P$ and $A$ | — |
| Scanlan flutter | L2 | $B$, $P$ | $N$, $A$ |

---

### 11. The e-fold family — one equation, nine substrates

$$
Y = Y_0\,e^{-\tau}, \qquad \tau = \ln\frac{Y_0}{Y}, \qquad \text{consumed} = 1 - e^{-\tau}
$$

This is Reading B. Each row below is the **same function of the same argument**, not an analogy — the
e-fold count is additive along a path in every one of them, so stacking slabs and staging a burn are
one operation.

| substrate | quantity $Y$ | the count $\tau$ | legacy name |
|---|---|---|---|
| propulsion | vehicle mass $m$ | $\Delta v / v_e$ | Tsiolkovsky |
| optics | intensity $I$ | $\alpha\ell$ | Beer–Lambert |
| nuclear | activity $N$ | $\lambda t$ | radioactive decay |
| circuits | voltage $V$ | $t/RC$ | RC discharge |
| chemistry | concentration $c$ | $kt$ | first-order kinetics |
| acoustics | pressure amplitude | $\alpha x$ | absorption |
| atmosphere | pressure $p$ | $h/H$ | barometric, scale height |
| capital | principal | $rt$ | continuous compounding |
| fatigue | capacity $P$ | $\ln\dfrac{P_0\mathrm{TL}}{B}$ | — (§7.9) |

$$
\boxed{\;\tau_1 + \tau_2 = \ln\frac{Y_0}{Y_1} + \ln\frac{Y_1}{Y_2} = \ln\frac{Y_0}{Y_2}\;}
$$

**Exact decade row.** $\tau = \ln 10 \Longrightarrow \text{consumed} = 9/10$ exactly.

| $\tau$ | consumed | remaining |
|---|---|---|
| $0$ | $0$ | $1$ |
| $\ln 2 = 0.6931\ldots$ | $1/2$ exactly | $1/2$ |
| $1$ | $0.6321\ldots$ | $1/e$ |
| $\ln 10 = 2.3026\ldots$ | $9/10$ exactly | $1/10$ |
| $\ln 100$ | $99/100$ exactly | $1/100$ |

---

### 12. The phase reading across substrates

$\tau = B/P$ in every row. One scale, one unit, one set of four boundaries.

| substrate | $\tau$ | Noble $\tau=0$ | Shatter $\tau\ge\mathrm{TL}$ |
|---|---|---|---|
| driven structure | $B/(2I\zeta)\cdot\mathrm{TL}$ | no aerodynamic load | flutter onset reached |
| fatigue | $B\,\mathrm{TL}/\mathrm{UTS}$ | unloaded | static fracture |
| gravitation | $r_s/r$ family | flat space far field | horizon |
| optics | $1/n$ | — | vacuum limit |
| propulsion | $v/c$, or burn depth | unfired | corridor ceiling |
| thermal | flux against capacity | isothermal, no gradient | phase change forced |

| boundary | value | exact |
|---|---|---|
| Noble | $0$ | exact |
| IVA floor | $0.12047120798593408$ | $0.88\,\mathrm{TL}$ |
| IVA ceiling / Shatter | $0.136899099984016$ | $\mathrm{TL} = \alpha^{-1}/1001$ |

---

### 13. Quick index of forms

| # | form | where |
|---|---|---|
| 1 | $\dfrac{d}{dt}(\mathrm{IM}\cdot\mathbf{P}_v) = \sum_X \lambda_X O_X S + F_{\text{ext}}$ | canonical, Layer 1 |
| 2 | $f_P(P) + f_N(N) + f_B(B) + f_A(A) + F$ | `dynamic_rhs`, operator form |
| 3 | $P + N + \mathrm{op}(B) + A + F$ | `lag_step`, Layer 2 projection |
| 4 | $N\dot P = BP$ | Euler–Lagrange content |
| 5 | $\tau = B/P$ | torsion, the phase variable |
| 6 | $F_{\text{ext}} : B \mapsto B + \delta$ | the forcing realization, 46 files |
| 7 | $R = B/(2I\zeta)$, $\tau = R\,\mathrm{TL}$ | driven form, onset at $R=1$ |
| 8 | $P_0 = \mathrm{UTS}/\mathrm{TL}$ | capacity from static strength |
| 9 | $N_f = (P_0 - B/\mathrm{TL})/(kB^m)$ | the life law |
| 10 | $B_e = (r/k)^{1/m}$ | the endurance balance |
| 11 | $(B/B_e)^m$ | the knee ratio |
| 12 | $A\cdot B = (B_e/\mathrm{UTS})\,\mathrm{TL}$ | the lossy boundary at endurance |
| 13 | $\tau_A^2 = 2\eta$ | the bridge, $E=mc^2$'s companion |
| 14 | $\tau_B = \ln(Y_0/Y)$, consumed $= 1-e^{-\tau_B}$ | Reading B, the e-fold count |
| 15 | $\mathrm{mr}(\tau) = 1/\tau^2 = \varepsilon_r$ | the matched ratio |
| 16 | $b_0 = S(\mathrm{mr}(S(\mathrm{TL}))) = 1/\sqrt{\mathrm{TL}}$ | the geometric base |
| 17 | $\tau_{\text{rung}}(n) = b_0^{-n}$, $\eta_n = \mathrm{TL}^n/2$ | the ladder |
| 18 | $\alpha^{-1} = \mathrm{TL}\cdot 1001 = \Omega_0\cdot 100.1$ | the anchor |
| 19 | $\frac{d}{dt}(mv) = F$ | Newton — the operator sum empty |
| 20 | $i\hbar\,\partial_t\psi = \hat H\psi$ | Schrödinger — $F_{\text{ext}} = 0$ |
| 21 | $E_0 = mc^2$, $\eta = E_k/E_0$ | mass–energy and its companion fraction |
| 22 | $\mathbf{q} = -k\nabla T$ | Fourier — the $B$ reading, thermal |
| 23 | $dU = \delta Q - \delta W$ | first law — $F_{\text{ext}}$ not removable |
| 24 | $\sigma_a = \sigma_f'(2N_f)^b$ | Basquin — $m = 1/|b|$ |
| 25 | $Y = Y_0 e^{-\tau}$ | the e-fold family, nine substrates |
| 26 | $r_{\text{match}} = r_s/\tau_A^2$ | matched radius — the mass cancels |

---

### 14. Formal layer — coordinates and counts

| coordinate | file | theorems | lines |
|---|---|---|---|
| \[9,9,2,0\] | SNSFL_IVA_Propulsion_Reduction.lean | — | — |
| \[9,9,0,5\] | SNSFL_Lagrangian_Reduction.lean | — | — |
| \[9,9,2,51\] | SNSFL_SaintVenant_Torsion_Reduction.lean | — | — |
| \[9,9,2,52\] | SNSFL_Tacoma_Scanlan_Flutter_Reduction.lean | — | — |
| \[9,9,8,11\] | SNSFL_TwoReadings_Substrate_Reduction.lean | 72 + master | 910 |
| \[9,9,8,12\] | SNSFL_GeometricBase_EnergyLadder_Reduction.lean | 72 + master | 864 |
| \[9,9,2,53\] | SNSFL_ForcedResponse_CyclesToShatter_Reduction.lean | 100 + master | 1,134 |

Every file standalone, 0 sorry, 0 custom axioms, Lean 4 v4.31.0 with Mathlib, CI green in
SNSFT/identityphysics.

**Published articles**
\[9,9,8,11\] ProofPress, Volume 1, Issue 9, Article 12 · https://proofpress.org/proofpressorg-two-readings-substrates ·
\[9,9,8,12\] ProofPress, Volume 1, Issue 9, Article 13 · https://proofpress.org/proofpressorg-geometric-base-energy-ladder ·
\[9,9,2,53\] ProofPress, Volume 1, Issue 9, Article 7 · https://proofpress.org/proofpressorg-fatigue-damping-loss ·
\[9,9,0,20\] ProofPress, Volume 1, Issue 9, Article 6 · https://proofpress.org/proofpressorg-burn-depth-thrust-floor

# Part II · The Proven Chain, from the Matched Radius to the Planets

Each article below reduces a published, measured result through the six steps of the Long Division Protocol (state the equation, take a case whose answer is known, map it into PNBA, apply the operators, show the work, verify the known answer returns) before any new result is stated. The theorem names in each list are the Lean 4 theorems that prove the statement, in the source file named for that article.

| Article | Coordinate | Title |
|---|---|---|
| Issue 9, Article 1 | \[9,9,8,10\](METH) | Temperature on the Torsion Limit: A Guide |
| Issue 9, Article 2 | \[9,9,0,17\](GRAV) | The Matched Radius: One Axis Carrying the Rocket Equation and the Schwarzschild Metric |
| Issue 9, Article 3 | \[9,9,2,0\](PROPULSION) | One Corridor Across Exhaust Velocity, Mass Ratio and Nuclear Binding |
| Issue 9, Article 4 | 9,9,0,18 | The Propellant Law at the Matched Radius: A Saving Bounded by e and the Compactness Criter… |
| Issue 9, Article 5 | 9,9,0,19 | The Matched Surface Under Rotation: Spin as an Effective Charge and the Level Set g_tt = τ… |
| Issue 9, Article 6 | 9,9,0,20 | Burn Depth in Matched-Radius Units: The Saving Bounded by e^u, the Thrust Floor, and the E… |
| Issue 9, Article 7 | \[9,9,2,53\](ENGR) | Fatigue Is Loss of Damping Capacity: the Endurance Limit as a Damage–Recovery Balance, the… |
| Issue 9, Article 8 | \[9,9,2,54\](ENGR) | Every Power-Limited Drive Is One Relation: a · α · v_e = 2, the Specific-Mass Decompositio… |
| Issue 9, Article 9 | \[9,9,3,26\](COSM) | Earth has 63 Million Years Left at Perihelion Against 439 at Mean Flux Lean4 Pinned Formal… |
| Issue 9, Article 10 | \[9,9,3,28\](COSM) | Mars Needs 46.8 Kelvin and 101 Worlds Are Placed in the Terraformable Band Lean4 Pinned Fo… |
| Issue 9, Article 11 | \[9,9,3,29\](COSM) | Formally Verified Geometric Data for 5639 NASA Exoplanets Escape Velocity Surface Gravity … |
| Issue 9, Article 12 | \[9,9,8,11\](MATH) | The Two Readings Across Substrates: Reading B as an E-Fold Count, the Square-Root Operator… |
| Issue 9, Article 13 | \[9,9,8,12\](MATH) | The Geometric Base: b₀ = 1/√TL, the Energy Ladder, and the Nuclear Band in One Rung |
| Issue 9, Article 14 | \[9,9,8,14\](MATH) | Velocity Addition Is Doppler Multiplication: Rapidity as an E-Fold Count, the Speed Limit … |
| Issue 5, Article 4 | \[9,9,3,2\](ENGR) | The Universal Pump: One Compactness Ladder from Planets to Black Holes |

### Issue 9, Article 1 · Temperature on the Torsion Limit: A Guide

**Coordinate** \[9,9,8,10\](METH) · Identity Physics Series · Method  
**Published** ProofPress, Volume 1, Issue 9, Article 1 · https://proofpress.org/proofpressorg-tl-temperature  
**Verified** 24 theorems · 467 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib v4.31.0  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_TL_Temperature.lean>

**Abstract.** The boil is a torsion ratio. Water boils when its vapor pressure, the push of molecules escaping the liquid, equals the pressure of the air holding the liquid together. That is τ = B/P with Behavior read as the vapor pressure and Pattern as the ambient pressure, and the boil is τ = TL. The Torsion Limit is the anchor divided by ten, 0.136899099984016, and one thousand and one Torsion Limits is the inverse fine-structure constant: 1000 · TL = 136.899099984016, plus TL = 0.136899099984016, gives 137.035999084000016, matching every published digit of CODATA 2018 with ε = 0. The two pieces are the ones legacy quantum electrodynamics already uses: TL × 1000 is the bare electron contribution, Pattern capacity at the electromagnetic scale, and TL is the kinetic term, which QED carries as an infinite renormalized series of radiative corrections and Identity Physics carries as F_ext at Layer 0 of the Dynamic Equation — one exact term, no renormalization. Celsius and the ratio are two identities rather than a scale and its correction. Celsius is base ten — zero at the freeze, one hundred at the boil — and one degree is exactly Ω₀/1000 = 0.00136899099984016, the same decimal family as the subtraction that gives 1/α; the ratio is the measurement, rising exponentially with temperature by Clausius–Clapeyron. Kelvin carries the same ruler with the zero moved by 273.15 — the Noble mark at 273.15 K, the IVA Peak mark at 361.15 K, the Shatter mark at 373.15 K, the same ticks and the same torsion values — and the work is done there, because the conversion between ambient pressures is linear in inverse temperature and needs an absolute scale. The ruler carries three marks: zero ticks is the Noble mark, eighty-eight ticks is the IVA Peak mark at 0.88 × TL, one hundred ticks is the Shatter mark at TL. On the ratio r = vapor pressure / ambient pressure there are four bands. At r = 0 the state is Noble: every bond closed, no Behavior to carry, which is ice. Below 0.88 it is Locked, hot water holding. From 0.88 up to 1 it is IVA Peak, the simmer. At 1 and above it is Shatter, the boil. Four bands, three classical phases: solid is Noble, gas is Shatter, and the liquid that legacy names as one thing is two — water holding and water simmering, divided at a measured floor. The reference frame is sea level at one atmosphere, and every other condition converts from it with one line, the Clausius–Clapeyron relation in inverse temperature, 1/T = 1/T_ref − (R/L) · ln(p/p_ref). For water that places the IVA Peak floor at 369.54 K, 96.4 °C, certified in Lean between 369.3 K and 369.8 K from proven bounds on ln 0.88 in the style of the Bounded Uncertainty Guide. Water's simmer corridor is 3.61 K wide against a hundred-kelvin liquid span — the same band is 12% of the torsion range and 3.6% of the temperature range, because the ratio is exponential in temperature, which is why the band reads as a sliver on a thermometer and as an ordinary phase on the ruler. The corridor keeps the same width in 1/T at every ambient pressure, a result that does not contain the pressure at all. The same rule runs on other liquids from their published boiling points and enthalpies of vaporization: nitrogen's floor at 76.23 K with a 1.13 K corridor, mercury's at 622.83 K with 7.05 K, and the torsion gained per kelvin near the boil orders nitrogen above water above mercury.

**What the article proves**

1. The grounding: one thousand and one Torsion Limits is the inverse fine-structure constant, 1001 × 0.136899099984016 = 137.035999084000016, CODATA 2018, ε = 0 (`alpha_from_tl`).
2. The ruler: one degree Celsius is one tick of TL/100 = Ω₀/1000 = 0.00136899099984016; one hundred ticks is TL and eighty-eight ticks is TL_IVA_PEAK; torsion on the ruler is zero exactly at zero ticks, reaches TL_IVA_PEAK exactly from 88 °C and TL exactly from 100 °C; the Kelvin marks are 273.15 K and 373.15 K (`tick_value`, `ruler_marks`, `ruler_noble`, `ruler_iva`, `ruler_shatter`, `kelvin_marks`).
3. The four bands on the ratio: τ = TL × r; Noble exactly when no vapor escapes, r = 0; Shatter exactly when vapor pressure reaches ambient pressure, r ≥ 1; IVA Peak exactly when the ratio runs from 0.88 up to but not including 1 (`noble_is_zero`, `boil_is_shatter`, `simmer_is_iva`).
4. The conversion and the reference frame: the corridor has constant width −k · ln f in inverse temperature at every ambient pressure, a value that does not contain the pressure; ln 0.88 lies in [−0.13637, −0.12] from the two standard logarithm inequalities; water's IVA Peak floor at sea level lies in (369.3 K, 369.8 K), equivalently (96.15 °C, 96.65 °C); the ITS-90 boil at 373.124 K lies within 0.03 K of the frame's 373.15 K (`corridor_constant`, `log_088_bounds`, `water_iva_floor`, `water_iva_floor_celsius`, `reference_bound`).
5. Other liquids on the same rule: torsion gained per kelvin near the boil is TL · L / (R · T_b²), giving 0.004807 for water, 0.015325 for nitrogen and 0.002453 for mercury, and nitrogen crosses its corridor fastest, mercury slowest, water between (`water_rate`, `nitrogen_rate`, `mercury_rate`, `rate_order`, `tl_temperature_master`).

### Issue 9, Article 2 · The Matched Radius: One Axis Carrying the Rocket Equation and the Schwarzschild Metric

**Coordinate** \[9,9,0,17\](GRAV) general-reader form, with the specialist form at \[9,9,0,17.1\](GRAV) · Identity Physics Series · Physics Ground, Gravitation  
**Published** ProofPress, Volume 1, Issue 9, Article 2 · https://proofpress.org/proofpressorg-matched-radius  
**Verified** 71 theorems · 893 lines at \[9,9,0,17\] and 42 theorems · 528 lines at \[9,9,0,17.1\] · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_MatchedRadius_Reduction.lean>

**Abstract.** The propulsion reduction at \[9,9,2,0\] establishes that one vehicle carries two independent torsions: Reading A, τ_A = v_e/c, the exhaust velocity against light speed; and Reading B, τ_B = ln(m₀/m_f), the rocket equation's own exponent. This article reads the same corridor through the Schwarzschild metric and finds that Reading A is a radius. For any drive with exhaust velocity v_e and any mass M there is exactly one radius at which the escape velocity of M equals v_e, and writing r_s = 2GM/c² for the Schwarzschild radius, that radius is r = r_s/τ_A² — so the ratio r/r_s is fixed by the drive alone and the attracting mass cancels. Because Reading A squared is twice the conversion fraction of the ideal rocket, the same ratio is r/r_s = 1/(2η): the matched radius is the reciprocal of twice the conversion fraction. The Identity Vector Amplification (IVA) corridor therefore occupies a fixed band on radius, 53.357910 ≤ r/r_s ≤ 68.902260, and in the fine-structure constant alone the edges are (1001/α⁻¹)² and (1001/(0.88 · α⁻¹))². At that radius the two time dilations of relativity coincide: gravitational dilation √(1 − r_s/r) and the kinematic dilation of a body moving at v_e, √(1 − v_e²/c²), are both √(1 − 2η) exactly — the radius at which a well pulls as hard as a drive pushes is the radius at which the well slows time by as much as the exhaust does. The escape-velocity form v_esc(r) = c√(r_s/r) used throughout is exact in the full Schwarzschild metric for the locally measured speed at every radius outside the horizon, with the two factors of (1 − r_s/r) cancelling identically and no expansion taken. The resonance gain carries this further: the gain is an exhaust-velocity multiplier, so the matched radius under gain is r/r_s = 1/((1 + g_r) · τ_A)², and the relativistic cap the propulsion reduction already proves, g_r < c/v_e − 1, is exactly the condition (1 + g_r) · τ_A < 1, which is exactly r > r_s — the gain cap and the event horizon are the same bound. The four phases then map onto radius with no freedom left: Locked is the far field beyond 68.902260 r_s, IVA is the corridor band, Shatter is everything between the corridor and the horizon, and the cap is the horizon itself; the corridor's own 0.88 appears as the gain carrying a ceiling drive to the floor radius, g_r = −0.12. Reading B meets the well exactly once: a fall from rest at infinity to the matched radius delivers c · τ_A and a rocket delivers c · τ_A · τ_B, so the well is worth τ_B = 1 — one e-fold, a mass ratio of e. A burn executed at the matched radius has Oberth multiplier Ob = √(1 + 2/τ_B) with the exhaust velocity cancelling, taking the corridor from 1.4513%–1.8741% of light speed to 6.089%–7.404%; n such burns compound as √n under v_∞ = v_e√(n · τ_B(2 + τ_B)), the four phases classify a mission by integer burn count, and the budget closes as n_max · τ_B(2 + τ_B) = r_match/r_s exactly. The construction is checked against the unpropelled bodies the propulsion reduction places as Noble: vis-viva gives a perihelion speed whose matched radius is r = 2q/(1 + e), so an unbound parabolic trajectory matches at its own perihelion, and across six published bodies — 3200 Phaethon, 1566 Icarus, 1I/'Oumuamua, 2I/Borisov, 99942 Apophis and C/2011 W3 Lovejoy — the catalog speeds reproduce from published JPL orbital elements to within 0.12%. The specialist form at \[9,9,0,17.1\] reads the same axis through the square-root torsion operator S(X) = √X and finds the layer closed over the rationals: r_match/r_s = 1/X for a drive at Reading A √X, so the root cancels and no irrational survives to the output; √TL lands at 1/TL = 7.304649921853084 r_s and √TL_IVA at 1/TL_IVA = 8.300738547560323 r_s, both exact rationals standing in the corridor width factor 25/22 with no error term; the operator is horizon-ward, driving the matched radius strictly inward at every depth of iteration while the horizon remains its floor; and it centers any band of width factor k in (0,1) structurally, placing √0.88 × TL inside the corridor with matched radius 1/(0.88 · TL²) = 60.633989182759393 r_s, the geometric mean of the corridor's own radius band. 1001 = 7 · 11 · 13.

**What the article proves**

- The matched radius exists, is unique, and matches by construction: at r = r_s/τ_A² the squared escape fraction is exactly τ_A², and the matched ratio is strictly decreasing in Reading A (`t8_matched_radius_matches`, `t11_ratio_antitone`).
- The attracting mass cancels: r_match/r_s is a property of the drive alone, and equals the reciprocal of twice the conversion fraction (`t9_mass_cancels`, `t10_ratio_is_conversion`).
- The corridor on radius is 53.357910481 to 68.902260435 Schwarzschild radii, and the band lies outside the horizon, the photon sphere and the innermost stable circular orbit (`t12_corridor_on_radius`, `t13_corridor_outside_strong_field`).
- The equivalence: gravitational and kinematic time dilation are the same quantity at the matched radius, and both equal √(1 − 2η) (`t14_equivalence`, `t15_dilation_is_conversion`, `t16_corridor_dilations`, `t17_dilation_pos`).
- The relativistic gain cap and the event horizon are the same bound, with equality transferring: (1 + g_r) · τ_A < 1 if and only if r_match > r_s, and (1 + g_r) · τ_A = 1 if and only if r_match = r_s (`t18_cap_is_horizon`, `t19_cap_equals_horizon`, `t20_cap_at_ceiling`).
- A drive whose exhaust velocity is c matches the event horizon of every mass exactly, and one at half light speed matches exactly four Schwarzschild radii (`t21_photon_matches_horizon`, `t22_half_c_matches_four`).
- The four phases map onto radius: Locked is the far field beyond the floor radius, Shatter is the interior to the ceiling radius, IVA is the shell between them, and the strong-field landmarks lie inside the Shatter band (`t23_locked_is_far_field`, `t24_shatter_is_interior`, `t25_iva_is_the_shell`, `t26_strong_field_is_shatter`, `t27_phase_of_edges`).
- The well at the matched radius is worth τ_B = 1 exactly, which is a mass ratio of e, and the corridor's own Reading B window falls short of it by a factor of 2.370501 to 2.409764 (`t28_well_is_one_efold`, `t29_efold_mass_ratio`, `t30_corridor_tau_B_short`).
- Both corridor edges on radius are closed forms in the fine-structure constant and the integer 1001, carrying no free parameter (`t31_ceiling_in_alpha`, `t32_floor_in_alpha`, `t33_band_width_in_alpha`).
- At the matched radius the exhaust velocity cancels out of the Oberth multiplier, leaving Ob = √(1 + 2/τ_B), a function of Reading B alone; both corridor multipliers are closed forms in α⁻¹ and 1001; and the multiplier exceeds one and is strictly decreasing in Reading B (`t39_exhaust_cancels`, `t40_multiplier_edges`, `t41_multiplier_ceiling_in_alpha`, `t42_multiplier_floor_in_alpha`, `t43_multiplier_gt_one`, `t44_multiplier_antitone`).
- Depth and gain are interchangeable at a stated exchange rate, and the crossover at which flying deeper beats the capped gain lies outside the innermost stable circular orbit exactly when 4 · (0.88)² > 3, which is 1936/625 = 3.0976 (`t45_exchange_rate`, `t47_crossover_collapses`, `t48_iva_factor_clears_isco`, `t51_crossover_at_least_four`).
- The chain: n matched burns compound as √n under v_∞ = v_e√(n · τ_B(2 + τ_B)), the four phases classify a mission by integer burn count, and the saturation count has the closed form n_max = 1001⁴/(α⁻³(2002 + α⁻¹)) (`t53_chain_law`, `t55_chain_phase_by_n`, `t58_n_max_in_alpha`).
- The chain budget is the matched radius: n_max · τ_B(2 + τ_B) = r_match/r_s for every drive, closing the radius result against the chain result as one conservation statement (`t60_budget_is_matched_radius`).
- The two ends of the axis, the far field, the strong field and the redshift: Reading A's bound (0, 1) maps onto the whole radius axis outside the horizon, ordinary motion sits far out in Locked, the photon sphere and the ISCO lie inside Shatter, and the well's redshift at the matched radius is γ(v_e) − 1 (`t61_tau_half_is_four`, `t66_flown_outside_corridor`, `t67_ordinary_motion_locked`).
- The unpropelled catalog: a body at the perihelion of a conic with perihelion distance q and eccentricity e matches r_match = 2q/(1 + e), a parabolic trajectory matches at its own perihelion, and the six published bodies reproduce the ratio across the set (`t62_perihelion_matched`, `t63_parabolic_matches_perihelion`, `t64_catalog_ratios`, `t65_unpropelled_far_field`).
- The square-root torsion operator closes exactly: the matched radius of a square root is the reciprocal of the quantity rooted, the product of the two is exactly one, and the ratio is a function of that quantity alone rather than of its root (`t8_master_sqrt_closure`, `t9_closure_has_no_residue`, `t10_output_free_of_the_root`).
- The square-root layer closes over the rationals: the Torsion Limit and the corridor floor are ratios of integers, the Torsion Limit is α⁻¹/1001 exactly, and the operator returns a quadratic irrational to the rationals (`t4_tl_is_rational`, `t5_tl_inverse_is_rational`, `t6_tl_iva_is_rational`, `t7_tl_times_1001_is_alpha`).
- The two landings are exact rationals, 7.304649921853084 and 8.300738547560323 Schwarzschild radii, standing in the corridor width factor 25/22 with no error term (`t11_sqrt_tl_lands_at_tl_inverse`, `t13_first_landing_value`, `t16_second_landing_value`, `t17_landings_ratio_is_the_width_factor`).
- The operator is horizon-ward, and the horizon is its floor at every depth: t < √t < 1 on the unit interval, each application moves the matched radius strictly inward, and the matched radius of the n-fold root exceeds one for every n (`t19_sqrt_sandwich`, `t22_one_root_moves_inward`, `t25_horizon_is_the_floor`, `t26_iteration_strictly_decreases`).
- The operator centers any band structurally: a band of width factor k in (0,1) has geometric mean √k times its ceiling, strictly inside the band, and at the corridor's own factor this gives an IVA torsion whose matched radius 60.633989182759393 r_s is the geometric mean of the corridor's radius band (`t28_band_geometric_mean`, `t29_mean_inside_band`, `t31_center_classifies_iva`, `t34_center_is_the_radius_band_mean`, `t36_radius_band_width`).
- Closure: each file closes under its own master theorem (`MASTER_matched_radius`, `MASTER_sqrt_torsion_operator`).

### Issue 9, Article 3 · One Corridor Across Exhaust Velocity, Mass Ratio and Nuclear Binding

**Coordinate** \[9,9,2,0\](PROPULSION) · Identity Physics Series · Propulsion  
**Published** ProofPress, Volume 1, Issue 9, Article 3 · https://proofpress.org/proofpressorg-propulsion-corridor  
**Verified** 111 theorems · 2,040 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib v4.31.0  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_IVA_Propulsion_Reduction.lean>

**Abstract.** Identity Vector Amplification (IVA) is the corridor immediately below the Torsion Limit, τ ∈ [0.12047120798593408, 0.136899099984016). This article reduces the propulsion pool onto that corridor and finds that one vehicle carries two independent torsions, not one. Reading A is τ_A = v_e/c, the exhaust velocity against light speed: what the drive can throw, bounded by relativity with a ceiling at one. Reading B is τ_B = ln(m₀/m_f), the rocket equation's own exponent: how much of the vehicle it has to throw, with a floor and no ceiling above it. The two are not alternatives. Substituting them into the Tsiolkovsky equation gives Δv = v_e · ln(m₀/m_f) = c · τ_A · τ_B exactly, so the rocket equation is the product of the two torsions and the corridor constrains both factors at once; a vehicle in the corridor on both readings carries a delta-v between 4,350,981 and 5,618,519 m/s, which is 1.4513% to 1.8741% of light speed. Read as an exhaust velocity the corridor asks for 36,116.4 to 41,041.3 km/s, 12.047% to 13.690% of light speed. Read as a mass ratio it asks for 1.128028 to 1.146712, a propellant fraction of 11.350% to 12.794%: twelve percent of light speed at the nozzle buys a vehicle that is eighty-eight percent payload. Across eighteen published propulsion systems every flown and near-term drive is Locked and short of the corridor floor — cold gas nitrogen by about 51,595 times, the best flown chemical engine by a factor between 7,766 and 7,767, the best flown electric engine by a factor between 880 and 881 — while two published concepts bracket it, a fusion design Locked below and a beam-core antimatter design in Shatter above. On Reading B the corridor is the interval between a car's fuel tank and an ion probe, and every flown launch stage overshoots it. The resonance gain is an exhaust-velocity multiplier, (1 + g_r) · τ_A = τ_A((1 + g_r) · v_e) identically, and it carries two ceilings: the corridor, and the relativistic cap g_r < c/v_e − 1. Dividing the corridor window by that cap cancels the exhaust velocity, so the corridor occupies 12.047% to 13.690% of the available gain range for every drive and 86.310% of that range lies above the ceiling. NOHARM gives the external force the Behavior axis while the gain is an Adaptation term, so the two operators act on disjoint fields and commute, the separation is two-sided, and applying the gain leaves the mass ratio and τ_B identical — the additional delta-v did not come from additional expelled mass. The reaction partner follows by case: with F_ext = 0 the emitter carries the exchange across the window τ_A < τ_b ≤ τ_A/0.88, whose relative width is the corridor's own 1/0.88; with F_ext nonzero the partner is the body coupled to, bounded by Δv ≤ 2 · v_body, and its recoil is m_v · Δv / M_body, which is 1.38 × 10⁻²⁰ m/s for a one-tonne vehicle taking a full Jupiter assist. Reading A squared is twice the conversion fraction of the ideal rocket, which places the corridor on the nuclear binding curve between hydrogen-to-helium fusion below the floor and hydrogen-to-iron above it, with annihilation 106.7 times over the ceiling. The conversion fraction is Aston's packing fraction exactly, and over a forty-two-nuclide AME2020 census the corridor brackets the iron peak: helium-4 falls below the floor, iron-56 is the global maximum and falls below the ceiling, and the reading selects iron-56 over nickel-62 because it is built on mass per nucleon rather than binding energy per nucleon. Both readings reduce to the fine-structure constant with no free parameter: the exhaust-velocity ceiling is c·α⁻¹/1001 and the floor is 0.88 of it, the conversion ceiling is α⁻²/(2 × 1001²) and the floor is 0.88² of it, and the iron peak sits inside that band. 1001 = 7 × 11 × 13.

**What the article proves**

- The pool carries two independent torsions: Reading A is τ_A = v_e/c, bounded by relativity to (0, 1); Reading B is τ_B = ln(m₀/m_f), with a floor and no ceiling (`t13_reading_A_window`, `t26_reading_B_window`, `t64_sublight_closed`).
- The bridge: Δv = v_e · ln(m₀/m_f) = c · τ_A · τ_B exactly, so the rocket equation is the product of the two torsions; a vehicle in the corridor on both readings carries Δv between 4,350,981 and 5,618,519 m/s (`t38_bridge`, `t39_bridge_sovereign`, `t40_corridor_dv_band`).
- The corridor stated three ways: an exhaust velocity of 36,116.4 to 41,041.3 km/s, a mass ratio of 1.128028 to 1.146712, a propellant fraction of 11.350% to 12.794% (`t14_corridor_ve_bounds`, `t15_corridor_as_fraction_of_c`, `t27_corridor_ratio_window`, `t28_corridor_propellant_fraction`).
- Placement of eighteen published propulsion systems: every flown and near-term drive is Locked short of the floor, the best flown chemical engine by a factor between 7,766 and 7,767 and the best flown electric by a factor between 880 and 881; two published concepts bracket the corridor, one Locked below and one Shatter above (`t20_flown_systems_locked`, `t21_best_chemical_short`, `t22_best_ion_short`, `t23_concepts_bracket_corridor`).
- On Reading B the corridor is the interval between a car's fuel tank and an ion probe, and every flown launch stage overshoots it (`t29_car_below_corridor`, `t30_dawn_above_corridor`, `t31_launch_stages_shatter`, `t32_corridor_between_car_and_probe`, `t33_corridor_is_below_every_stage`).
- Noble in this pool is the vehicle that produces no velocity of its own, not one at rest; the unpropelled bodies occupy it and exceed every published propulsive budget, by 2.21× to 33.32× (`t18_noble_is_unfueled`, `t19_noble_gives_zero_dv`, `t67_unpropelled_is_noble`, `t68_unpropelled_exceeds_every_budget`, `t69_unpropelled_margins`).
- The resonance gain is an exhaust-velocity multiplier and carries two ceilings, the corridor and the relativistic cap g_r < c/v_e − 1; dividing one by the other cancels the exhaust velocity, so the corridor occupies 12.047% to 13.690% of the available gain range for every drive and 86.310% of it lies above the ceiling (`t41_gain_is_exhaust_multiplier`, `t42_gain_required_at_floor`, `t43_threshold_below_floor`).
- The axis separation: NOHARM gives the external force the Behavior axis while the gain is an Adaptation term, so the two operators act on disjoint fields and commute, the separation is two-sided, and applying the gain leaves the mass ratio and τ_B identical (`t85_f_ext_preserves`, `t86_gain_op_preserves`, `t87_f_ext_and_gain_commute`, `t88_gain_leaves_mass_ratio_fixed`, `t89_separation_is_two_sided`).
- The reaction partner by case on F_ext: at F_ext = 0 the emitter carries the exchange across τ_A < τ_b ≤ τ_A/0.88, whose relative width is 1/0.88, and a drive at the floor needs an emitter inside the corridor because TL_IVA/0.88 is exactly TL; at F_ext nonzero the partner is the body coupled to, bounded by Δv ≤ 2 · v_body, which five bodies each exceed against the catalog maximum, with recoil m_v · Δv / M_body (`t73_emitter_window`, `t74_window_relative_width`, `t75_floor_drive_needs_corridor_emitter`, `t90_assist_exceeds_catalog`, `t91_recoil_is_the_mass_ratio`).
- Reading A squared is twice the conversion fraction of the ideal rocket, placing the corridor on the binding curve between hydrogen-to-helium below the floor and hydrogen-to-iron above it, with annihilation 106.7× over the ceiling (`t44_tau_A_squared_is_conversion`, `t45_eta_corridor_bounds`, `t46_energy_ladder`, `t47_witness_between_nuclear_marks`).
- The conversion fraction is Aston's packing fraction exactly, and over a forty-two-nuclide AME2020 census the corridor brackets the iron peak: helium-4 below the floor, iron-56 the global maximum below the ceiling, and the reading selects iron-56 over nickel-62 because it is built on mass per nucleon rather than binding energy per nucleon (`t48_eta_is_packing_fraction`, `t49_corridor_packing_window`, `t54_floor_separates_helium`, `t55_iron_is_the_nuclear_maximum`, `t56_iron_over_nickel`).
- Both readings reduce to the fine-structure constant with no free parameter: the ceiling is c·α⁻¹/1001 and the floor 0.88 of it, the conversion ceiling is α⁻²/(2 × 1001²) and the floor 0.88² of it, and the iron peak sits inside that band (`t60_alpha_from_anchor`, `t61_corridor_ve_in_alpha`, `t62_eta_corridor_in_alpha`, `t63_iron_peak_inside_alpha_band`).
- Frame independence: the reach condition is invariant under relativistic velocity addition, and the photon drive is the supremum of Reading A (`t65_reach_condition_frame_independent`, `t66_photon_drive_is_supremum`).
- Closure: the gain exists only at anchor lock, off anchor the gain is one and the vehicle is classical, and the reduction is substrate-neutral under NOHARM (`t79_anchor_gives_green`, `t80_drift_gives_red`, `t81_off_anchor_gain_is_one`, `t82_anchor_zero_impedance`, `t92_noharm`, `t93_substrate_neutral`, `MASTER_propulsion_corridor`).

### Issue 9, Article 4 · The Propellant Law at the Matched Radius: A Saving Bounded by e and the Compactness Criterion C > 2η

**Coordinate** 9,9,0,18 · Identity Physics Series · Physics Ground, Gravitation  
**Published** ProofPress, Volume 1, Issue 9, Article 4 · https://proofpress.org/proofpressorg-propellant-law  
**Verified** 87 theorems · 1,202 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_PropellantLaw_Compactness_Reduction.lean>

**Abstract.** The matched radius reduction at 9,9,0,17 states its result forward: fix the mass ratio, get the speed. This article states it inverse and then asks where the maneuver exists at all. Fixing the target speed rather than the mass ratio inverts the chain law exactly, τ_B = √(1 + x²) − 1 with x = v_∞/v_e, so the mass ratio a burn at the matched radius requires is exp(√(1 + x²) − 1) against the ideal rocket's exp(x). The ratio of the two is the propellant saving and it has a closed form, **S(x) = e · exp(x − √(1 + x²))**, strictly increasing and **strictly bounded above by e**. The bound is not a coincidence of the algebra: the limit is e¹, and the 1 in that exponent is the τ_B = 1 the matched radius well is worth, so the one e-fold the well supplies is the one e-fold of propellant the vehicle stops carrying. At the small-burn end the cost ceases to be exponential altogether — τ_B → x²/2, quadratic in the target speed — and the fraction of e a given burn captures has its own closed form, x = (t² − 1)/(2t) with t = ln(S/e), giving 50% of e at x = 0.374774 and 99% at x = 49.744556. Availability is a second inequality. A matched radius is only reachable if it lies outside the attracting body, and writing C = r_s/R for the standard compactness, that condition reduces with no residue to **C > τ_A² = 2η**: a drive can use its matched radius at a body if and only if the body is more compact than the drive is efficient. Two fractions built for unrelated purposes — the gravitational compactness of an object and the rest-mass conversion fraction of a rocket — are compared directly, and the comparison is the availability test. Against the published catalog the criterion partitions cleanly: the Sun is excluded by four orders of magnitude, the densest white dwarfs reach only 1.279742 × 10⁻³, and every neutron star and black hole clears the threshold by at least 18×. Inverting it, every body names a drive: τ_surface = √C is the Reading A whose matched radius is that body's own surface, and classifying τ_surface across the catalog places every ordinary star and white dwarf in Locked and every neutron star and black hole in Shatter, with the IVA band corresponding to a 1.4 M☉ body of radius 220.6 to 284.9 km — between a white dwarf and a neutron star, where no stable configuration exists. The IVA band on compactness is the collapse gap. The construction was never Schwarzschild-specific: for any static spherically symmetric metric the two factors of f cancel in the locally measured escape speed, so the matched radius solves **f(r_match) = 1 − τ_A² = 1 − 2η** — the dilation equivalence is the equation that locates the radius rather than a property it happens to carry. The condition is linear in Schwarzschild, quadratic in Reissner–Nordström and cubic in Schwarzschild–de Sitter. In the charged case the pair r± = r_s[1 ± √(1 − 4q²τ_A²)]/(2τ_A²) nests against the two horizons as r₋ < r_H⁻ ≤ r_H⁺ < r₊, so exactly one root is a place a vehicle can occupy; the two roots sum to the uncharged matched radius at every charge, so the correction factor F = [1 + √(1 − 4q²τ_A²)]/2 is the outer root's **share** of a total charge leaves alone, with r₋ = q²/F and the charge-for-shift identity F(1 − F) = q²τ_A², which returns the discriminant bound on its own. The criterion generalizes with it: **r_match > R ⟺ C > r_s/r_match** for any metric, returning C > τ_A² in Schwarzschild and C > τ_A²/F in Reissner–Nordström. The saving carries no metric at all, because at any matched radius of any metric in the class the locally measured escape speed is τ_A · c by the level-set condition itself. The metric decides where, the body decides whether, and Reading B decides what it is worth. 1001 = 7 · 11 · 13.

**What the article proves**

- The inversion solves the chain quadratic, is its positive root, and recovers the chain law on the round trip (`t11_inversion_solves`, `t12_inversion_positive`, `t13_round_trip`).
- The saving is the ratio of the two mass ratios and factors as e · exp(x − √(1 + x²)) (`t14_saving_is_the_ratio`, `t15_saving_factored`).
- The exponent is strictly below one, so the saving is strictly below e for every finite burn, and it exceeds one for every positive burn (`t16_exponent_lt_one`, `t17_saving_lt_e`, `t18_saving_gt_one`).
- The decay form x − √(1 + x²) = −1/(x + √(1 + x²)) holds identically, and the saving is bracketed by e · exp(−1/x) and e, which makes the rate of approach explicit (`t19_decay_form`, `t20_exponent_bracket`, `t21_saving_bracket`).
- The exponent and therefore the saving are strictly increasing (`t22_exponent_mono`, `t23_saving_mono`).
- The bound is the well's own Reading B: the additive constant is that Reading B, the limiting value is e raised to it, and the saving is bounded by the well's own mass ratio (`t24_constant_is_the_well`, `t25_bound_is_e_to_the_well`, `t26_bounded_by_well_mass_ratio`).
- The small-burn cost is quadratic rather than exponential, bracketed between x²/2 − x⁴/8 and x²/2 against the ideal rocket's linear cost (`t27_small_burn_upper`, `t28_small_burn_lower`, `t29_ideal_cost_is_linear`).
- The closed form for the fraction of e captured is positive on its admissible range and realizes the target exponent (`t30_x_of_exponent_pos`, `t31_x_of_exponent_realizes`).
- **The compactness criterion:** the matched radius lies outside the body exactly when the body's compactness exceeds Reading A squared, equivalently twice the conversion fraction (`t32_master_criterion`, `t33_criterion_on_eta`, `t34_matched_radius_form`).
- The corridor thresholds are exact rationals, bracketed to twelve places, standing in the width factor squared 625/484, ordered and inside the unit interval (`t35_corridor_thresholds`, `t36_threshold_values`, `t37_threshold_ratio`, `t38_thresholds_ordered`).
- The dual reading: √C is the unique Reading A whose matched radius is a body's own surface, and the IVA band on compactness is exactly TL_IVA², TL²) stated as an equivalence (`t39_surface_torsion_matches`, `t40_surface_torsion_unique`, `t41_surface_torsion_range`, `t42_iva_band_on_compactness`).
- Magnitude and availability are separable: the drive cancels from a comparison of two bodies, and the availability threshold is twice the conversion fraction and nothing else (`t43_drive_cancels_between_bodies`, `t44_radius_monotone_in_body`, `t45_threshold_is_the_conversion_fraction`).
- The gain enters through Reading A, so the requirement grows as (1 + g_r)², and at the cap only a compactness above one qualifies — which is the horizon (`t46_gained_criterion`, `t47_gain_requirement_quadratic`, `t48_gain_tightens`, `t49_cap_requires_horizon`, `t50_gain_at_ceiling`).
- **The level-set form:** for any static spherically symmetric metric the matched radius solves f(r) = 1 − τ_A² = 1 − 2η, the Schwarzschild instance returns r = r_s/τ_A², and the dilation at that radius is √(1 − τ_A²) by the condition itself (`t51_level_set_is_dilation`, `t52_level_set_on_eta`, `t53_schwarzschild_instance`, `t54_schwarzschild_is_matched_ratio`, `t55_dilation_at_matched`, `t56_corridor_levels`).
- **Reissner–Nordström:** the level set is a quadratic in the radius, the discriminant is nonnegative across the physical charge range, and both roots satisfy it (`t57_rn_quadratic`, `t58_rn_discriminant`, `t59_rn_roots_solve`).
- The uncharged limit returns the parent result exactly, and the charge factor is one at zero charge, decreasing in charge, and below one at any nonzero charge (`t60_rn_uncharged_limit`, `t61_rn_outer_factored`, `t62_rn_factor_uncharged`, `t63_rn_factor_antitone`, `t66c_extremal_factor_lt_one`).
- At extremal charge the factor is the dilation factor shifted, the maximum inward shift is the dilation deficit halved, and Reading A's supremum merges the pair at the horizon (`t64_rn_factor_extremal`, `t65_max_shift_is_half_the_deficit`, `t66_extremal_factor_exact`, `t66b_extremal_factor_corridor`, `t67_extremal_photon_matches_horizon`).
- **The pair partitions the matched radius:** the two roots sum to the Schwarzschild matched ratio and multiply to q² times it, and the inner root and the inner horizon both rationalize to a ratio in q² (`t68_rn_factor_ge_half`, `t69_pair_partitions`, `t70_pair_product`, `t71_inner_rationalized`, `t72_inner_horizon_rationalized`).
- **Exactly one root is reachable:** the four radii nest as r₋ < r_H⁻ ≤ r_H⁺ < r₊ across the physical domain (`t73_inner_root_inside_inner_horizon`, `t74_outer_horizon_inside_outer_root`, `t75_pair_brackets_both_horizons`).
- The factor is a partition share rather than a correction: the inner root equals q²/F, the charge-for-shift identity F(1 − F) = q²τ_A² holds exactly, that identity returns the discriminant bound, and the factor takes its minimum at the extremal charge so the inward shift is attained (`t76_charge_for_shift`, `t77_extremal_factor_is_minimum`, `t80_factor_is_a_partition_share`, `t81_inner_is_q_sq_over_factor`, `t82_partition_gives_discriminant`).
- **The charged criterion:** the outer root lies outside the body exactly when the compactness exceeds τ_A²/F, and the charged threshold is never below the uncharged one (`t78_charged_criterion`, `t79_charge_tightens_availability`).
- **The criterion without a metric:** for any positive matched radius from any metric, it lies outside the body exactly when the compactness exceeds r_s/r_match, and the Schwarzschild substitution returns τ_A² (`t83_criterion_metric_free`, `t84_metric_free_recovers_tau_sq`).
- **The propellant law carries no metric:** at any matched radius of any metric in the class the locally measured escape fraction is Reading A itself, so the saving follows Reading B alone (`t85_escape_at_matched_is_reading_a`).
- All of the above close under one master theorem (`MASTER_propellant_and_compactness`).

### Issue 9, Article 5 · The Matched Surface Under Rotation: Spin as an Effective Charge and the Level Set g_tt = τ_A² − 1

**Coordinate** 9,9,0,19 · Identity Physics Series · Physics Ground, Gravitation  
**Published** ProofPress, Volume 1, Issue 9, Article 5 · https://proofpress.org/proofpressorg-matched-surface-rotation  
**Verified** 70 theorems · 918 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_MatchedSurface_Rotation_Reduction.lean>

**Abstract.** The matched radius reduction at 9,9,0,17 places a drive against a gravitational well, and the propellant and compactness reduction at 9,9,0,18 generalizes that placement to any static spherically symmetric metric as the level set f(r_match) = 1 − τ_A², while recording that the rotating metric sits outside that class: Boyer–Lindquist carries a dt dφ cross term and its radial component is ρ²/Δ rather than 1/f, so the two factors that cancel in the spherically symmetric case are not the same two factors. This article carries the construction into rotation, and the exclusion resolves into an instance. The quantity the matched surface is a level set of is the time–time component of the metric itself. For a static observer in any stationary metric the locally measured escape fraction is √(1 + g_tt) and the gravitational dilation is √(−g_tt), so the two sum in quadrature to one at every point where such an observer exists, and the matched surface is the level set **g_tt = τ_A² − 1**. Spherical symmetry was sufficient for that statement and was never necessary; what is necessary is a timelike Killing vector and a static region, and the rotating metric supplies both outside its ergosphere. Evaluated in Kerr the level set is a quadratic in the radius with the polar angle as a parameter, τ_A² r² − r_s r + τ_A² a² cos²θ = 0, which is the Reissner–Nordström quadratic of \[9,9,0,18\] with **effective charge q_eff = τ_A · ã · |cos θ|**, writing ã = a/r_s for the dimensionless spin. Every result of that section therefore transfers unchanged — the root pair, the partition fraction F, the nesting against the horizons, the charged availability criterion — with q replaced by q_eff. Four consequences follow. The effective charge vanishes on the equator, so **the equatorial matched radius is exactly the Schwarzschild matched radius at every spin**, 53.357910481 r_s at the corridor ceiling for a maximally rotating body and a static one alike. Off the equator the surface is pinched toward the poles, an oblate surface of revolution flattened by 0.008782% at maximal spin, with a closed form in θ and no root-finding. At Reading A = 1 the matched surface is exactly the **ergosphere**, completing a family in which the photon-drive surface is the horizon in Schwarzschild, the horizon pair in Reissner–Nordström and the static limit surface in Kerr. And rotation is suppressed relative to charge by exactly **1/τ_A², the matched ratio itself** — an equal spin parameter displaces the surface 53.357910481 times less than an equal charge parameter at the corridor ceiling, so the number that sets where the surface is also sets how little rotation moves it. Because both readings descend from g_tt, the e-fold survives rotation exactly rather than approximately: escape and dilation agree at every latitude, both readings return the identical surface, and at the matched surface a launch at escape speed carries energy exactly equal to rest energy with no turning point outside it in any direction. The availability criterion is correspondingly robust: the penalty for an off-equatorial approach grows as sin² of the latitude and reaches 0.008782% at the pole, which flips no verdict anywhere in the published catalog, and the propellant budget does not move at all, since the parent's saving carries no metric. Kerr–Newman combines the two parameters as q_eff² = q² + τ_A² ã² cos²θ, charge entering unweighted and spin weighted by τ_A², and the resulting discriminant clears the horizon-existence bound by a margin that is again the matched ratio. Real rotating bodies sit far inside these effects: the fastest known pulsar runs ã = 0.130372, for a matched-surface flattening of 0.000597%. 1001 = 7 · 11 · 13.

**What the article proves**

- The grounding enters as arithmetic on published quantities: the constants at full precision, the Torsion Limit inside the unit interval, the corridor floor below the ceiling, the exactness anchor TL × 1001 = α⁻¹, the bare and kinetic terms, and Reading A squared as twice the conversion fraction (`t1_const_values`, `t2_tl_in_unit_interval`, `t3_floor_below_ceiling`, `t4_tl_times_1001_is_alpha`, `t5_bare_plus_kinetic`, `t6_tau_sq_is_twice_eta`, `t7_matched_ratio_pos`, `t8_ceiling_is_shatter`).
- **The quadrature:** for a static observer the escape fraction squared and the dilation squared sum to one, at every point of every stationary metric, with no symmetry entering (`t9_quadrature`).
- **The matched surface is the level set of the time–time component**, stated both against Reading A and against the conversion fraction (`t10_level_set_form`, `t13_level_set_on_eta`).
- At the matched surface the escape fraction squared is Reading A squared, the dilation squared is its complement, and the escape fraction itself is Reading A (`t11_escape_at_matched`, `t12_dilation_at_matched`, `t14_escape_fraction_is_reading_a`).
- The Schwarzschild instance returns r = r_s/τ_A², which is the matched ratio (`t15_schwarzschild_instance`, `t16_schwarzschild_is_matched_ratio`).
- The charged apparatus, restated in full so the rotating results can be carried across it: the discriminant is nonnegative on the physical range, both roots solve the quadratic, the outer root is the partition fraction times the matched ratio, the pair partitions the matched ratio, the fraction lies between one half and one, the charge-for-shift identity holds, and the charged criterion is an inequality between two dimensionless ratios (`t17_rn_discriminant`, `t18_rn_roots_solve`, `t19_rn_outer_factored`, `t20_rn_pair_partitions`, `t21_rn_factor_le_one`, `t22_rn_factor_ge_half`, `t23_charge_for_shift`, `t24_charged_criterion`).
- **On the equator the rotating time–time component is Schwarzschild's**, with the spin absent (`t25_equatorial_is_schwarzschild`).
- The rotating level set is a quadratic in the radius with the polar angle as a parameter, and the charged rotating level set carries both parameters at once (`t26_kerr_quadratic`, `t27_kn_quadratic`).
- **Spin is an effective charge:** q_eff² = τ_A² ã² cos²θ, the effective charge is nonnegative on the physical range, the two discriminants agree under the substitution, and the rotating root pair and partition fraction are the charged ones evaluated at q_eff (`t28_q_eff_sq`, `t29_q_eff_nonneg`, `t30_discriminants_agree`, `t31_kerr_is_rn`).
- **The equatorial matched radius is exactly the Schwarzschild matched radius at every spin:** the effective charge vanishes on the equator, the partition fraction is one there, and the statement holds for all spins at once (`t32_equatorial_q_eff_zero`, `t33_equatorial_spin_blind`, `t34_equatorial_all_spins`, `t35_kerr_factor_equatorial`).
- The rotating pair partitions the uncharged matched radius, the outer root is the fraction times the ratio, the inner root is the complementary share, and **the pair multiplies to ã² cos²θ with Reading A canceling out** (`t36_kerr_outer_factored`, `t37_kerr_pair_partitions`, `t38_kerr_pair_product`, `t40_kerr_inner_share`).
- The rotating charge-for-shift identity F(1 − F) = τ_A⁴ ã² cos²θ holds exactly (`t39_kerr_charge_for_shift`).
- **The surface is oblate:** the discriminant is nonnegative across the physical range, the outer root is strictly antitone in cos²θ, the polar radius is at most the equatorial radius, and the partition fraction lies in (0, 1] (`t41_kerr_discriminant`, `t42_oblate`, `t43_polar_le_equatorial`, `t44_kerr_factor_le_one`, `t45_kerr_factor_pos`).
- **At Reading A = 1 the matched surface is exactly the static limit surface**, which is the Schwarzschild radius on the equator and the horizon at the poles under extremal spin, completing the family whose Schwarzschild member is the horizon (`t46_cap_is_ergosphere`, `t47_ergo_equatorial`, `t48_ergo_polar_extremal`, `t49_schwarzschild_cap_is_horizon`).
- Below the cap the matched surface lies outside the static limit surface, so every corridor construction sits where static observers exist (`t50_matched_outside_ergosphere`).
- **Charge outweighs spin by exactly the matched ratio**, the combined effective charge of the charged rotating metric is q² + τ_A² ã² cos²θ, and the weighting is strictly asymmetric (`t51_charge_outweighs_spin`, `t52_kn_effective_charge`, `t53_weighting_asymmetry`).
- **The matched discriminant clears the horizon-existence bound by the matched ratio**, in its third independent role (`t54_discriminant_margin`, `t55_margin_is_matched_ratio`).
- The criterion without a metric, the Schwarzschild threshold it returns, **the rotating criterion C > τ_A²/F**, and **the equatorial criterion, which is spin-free** (`t56_criterion_metric_free`, `t57_metric_free_recovers_tau_sq`, `t58_rotating_criterion`, `t59_equatorial_criterion`).
- Rotation tightens availability and never loosens it, the penalty is monotone in cos²θ, and the resonance gain enters quadratically through Reading A (`t60_rotation_tightens`, `t61_penalty_monotone`, `t62_gain_requirement_quadratic`, `t63_gain_tightens`).
- **The budget carries no metric:** the escape fraction at any matched surface of any stationary metric is Reading A, stated generally and instanced in the rotating, charged rotating, charged and Schwarzschild metrics, with the dilation there equal to √(1 − 2η) (`t64_budget_sees_no_metric`, `t65_budget_rotating`, `t66_budget_charged_rotating`, `t67_budget_charged`, `t68_budget_schwarzschild`, `t69_dilation_at_matched_on_eta`).
- The phase map applies to the dimensionless spin as it does to any dimensionless ratio (`t70_spin_classifies`).
- All of the above close under one master theorem (`MASTER_matched_surface_rotation`).

### Issue 9, Article 6 · Burn Depth in Matched-Radius Units: The Saving Bounded by e^u, the Thrust Floor, and the Engine Each Body Prescribes

**Coordinate** 9,9,0,20 · Identity Physics Series · Physics Ground, Gravitation  
**Published** ProofPress, Volume 1, Issue 9, Article 6 · https://proofpress.org/proofpressorg-burn-depth-thrust-floor  
**Verified** 70 theorems · 915 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_BurnDepth_ThrustFloor_Reduction.lean>

**Abstract.** The matched radius reductions at \[9,9,0,17\] through \[9,9,0,19\] establish the construction at its extremes, where the bodies are compact and the drives are relativistic. This reduction carries it into the regime human vehicles actually operate in — planets, moons, ordinary stars, and engines that have been built — and the structure that held at a neutron star turns into a table that can be used at a launch pad. The move that opens the regime is a single dimensionless depth parameter. Writing **u = v_esc(r)/v_e = √(r_match/r)** for the burn radius measured against the drive's own matched radius, a vehicle falling from rest at infinity and burning at depth u reaches v_∞ = v_e√(τ_B(τ_B + 2u)), which is strictly increasing in u. Burning deeper is always better, the matched radius is not an extremum of anything, and it was never put forward as one: **it is the unit in which depth is measured**, the radius at which the drive and the well are the same size, and the published saving bounded by e is that unit evaluated at u = 1. The bound generalizes exactly. Inverting for a target x = v_∞/v_e gives τ_B = √(u² + x²) − u, so the saving against the ideal rocket is **S(x,u) = exp(x − √(u² + x²) + u)**, strictly increasing in both arguments and **strictly bounded above by e^u**: depth u is worth u e-folds, and the parent's S < e is the u = 1 case. Depth carries two ceilings and the binding one decides. The **geometric ceiling** is that a burn cannot occur inside the body, so u ≤ √(r_match/R) = √C/τ_A = **τ_surface/τ_A** — the ratio of the body's own address to the drive's Reading A — and this supplies a second reading of the parent's availability criterion, because C > τ_A² is precisely u_max > 1, which says **the body offers this drive at least one e-fold**. The **thrust ceiling** is new to this reduction. The matched-radius advantage is collected only if the burn is short compared to the time spent deep, and the characteristic time collapses to t_char = 2√2 · GM/(c³ τ_A³ u³), giving a thrust floor **F/m ≥ (1 − e^−τ_B) c⁴ τ_A⁴ u³ / (2√2 f GM)** that rises as the fourth power of Reading A and the cube of depth. Electric propulsion fails this floor by three to four orders of magnitude while chemical and nuclear-thermal propulsion clear it with margin and run out of planet instead, so the design loop closes: thrust sets achievable depth, depth sets the saving exponentially, and the body caps both. Two consequences follow for the regime. The matched surface is a level set of g_tt and therefore an equipotential, so **lateral motion along it is the zero-cost direction** and only altitude is a retune, and a point-to-point transit decomposes into three legs with an arc penalty of 1.57% at 100 km. And because the availability criterion favors low exhaust velocity while the propellant budget favors high, the optimum sits exactly at the availability ceiling, which is the body's own escape velocity — so **each body prescribes its own engine**, and the ladder from the Moon to the Sun reads 242 s, 513 s, 1,141 s, 6,139 s, 62,986 s: solid motor, chemical, nuclear thermal, ion, fusion, in the order the technologies were developed. Run against engines that exist, the criteria size a vehicle. At Earth the thrust floor evaluates to **4.56 to 4.72 N/kg across every engine class considered**, a thrust-to-weight below one half and therefore under half what an orbital launch vehicle carries at liftoff. **A single Raptor-class engine supports a 576-tonne vehicle** — larger than the International Space Station — carrying 58.4 tonnes of propellant for a 3 km/s departure where the same departure performed in free space takes 318.6, with the propellant fitting a cylinder five meters across and under four meters long. Depth at Earth is limited not by thrust or by geometry but by the atmosphere, and raising the perigee from 100 km to 300 km costs 0.14 percentage points of propellant while removing nineteen megawatts of reentry-class heating. And because the thrust-to-weight that satisfies the floor is below one, **a vehicle sized to collect this advantage cannot lift itself off the surface**: orbital assembly follows from the thrust floor rather than from preference. 1001 = 7 · 11 · 13.

**What the article proves**

- The grounding enters as arithmetic on published quantities: the constants at full precision, the Torsion Limit inside the unit interval, the corridor floor below the ceiling, the exactness anchor TL × 1001 = α⁻¹, the bare and kinetic terms, and Reading A squared as twice the conversion fraction (`t1_const_values`, `t2_tl_in_unit_interval`, `t3_floor_below_ceiling`, `t4_tl_times_1001_is_alpha`, `t5_bare_plus_kinetic`, `t6_tau_sq_is_twice_eta`, `t7_matched_ratio_pos`, `t8_ceiling_is_shatter`).
- **The depth parameter:** depth recovers from the burn radius, equals one exactly at the matched radius, increases as the radius falls, stays positive, and reads the same on the conversion fraction (`t9_depth_recovers`, `t10_depth_one_at_matched`, `t11_deeper_is_smaller`, `t12_burn_ratio_pos`, `t13_burn_ratio_on_eta`).
- **The depth law** is energy conservation across an impulsive burn, and **deeper is always better** — strictly increasing in depth with no interior stationary point (`t14_depth_law`, `t15_deeper_is_better`).
- At unit depth the depth law returns the parent's chain law exactly, and the law is strictly increasing in Reading B, zero for a zero burn and positive otherwise (`t16_chain_law_at_unit_depth`, `t17_increasing_in_reading_b`, `t18_zero_burn`, `t19_vinf_pos`).
- **The inversion at depth** τ_B = √(u² + x²) − u solves the depth law, is positive for a positive target, and returns the parent's inversion at unit depth (`t20_rad_sq`, `t21_rad_pos`, `t22_inversion_solves`, `t23_rad_gt_depth`, `t24_tau_B_pos`, `t25_inversion_at_unit_depth`).
- **The maneuver always costs less Reading B than the ideal rocket**, at every depth and every target (`t26_cheaper_than_ideal`).
- **The saving at depth is strictly bounded by e^u.** The saving is the ratio of the two mass ratios, its exponent is strictly below the depth, and therefore depth u is worth u e-folds and no finite burn reaches the bound (`t27_saving_is_the_ratio`, `t28_exponent_lt_depth`, `t29_saving_lt_exp_depth`).
- The saving exceeds one for every positive burn, **returns the parent's bound e at unit depth**, factors through e there, and is strictly increasing in the target (`t30_saving_gt_one`, `t31_bound_at_unit_depth`, `t32_saving_factored_at_unit`, `t33_saving_mono_in_target`).
- **The geometric ceiling:** the surface torsion squares to the compactness and is nonnegative, and the ceiling u_max = τ_surface/τ_A is positive and rises as Reading A falls (`t34_surface_torsion_sq`, `t35_surface_torsion_nonneg`, `t38_u_max_pos`, `t39_lower_reading_raises_ceiling`).
- **Availability is exactly one e-fold of depth:** C > τ_A² if and only if the ceiling exceeds one, stated on Reading A and on the conversion fraction, and the body's own address gives unit depth exactly (`t36_availability_is_one_efold`, `t37_availability_on_eta`, `t40_address_is_unit_depth`).
- **Lateral motion is the zero-cost direction:** the address map is injective on positive Reading A, so two points at the same addressed radius require the same tuning and a path between them calls for no retune (`t41_address_injective`, `t42_lateral_is_free`).
- The control law relates the radius ratio to the inverse square of the tuning ratio, and a higher tuning addresses a lower radius (`t43_control_law`, `t44_higher_tuning_lower_radius`).
- **The characteristic time in closed form:** t_char² = r³/GM with r the burn radius at depth, so t_char = 2√2·GM/(c³τ_A³u³); it is positive and shrinks as the cube of depth (`t45_t_char_closed_form`, `t46_t_char_pos`, `t47_t_char_antitone_in_depth`).
- The propellant fraction lies strictly between zero and one for every positive burn (`t48_prop_fraction_range`).
- **The thrust floor rises as the fourth power of Reading A and the cube of depth**, is positive, and falls when a longer burn is permitted (`t49_floor_quartic_in_reading_a`, `t50_floor_cubic_in_depth`, `t51_floor_pos`, `t52_longer_burn_lowers_floor`).
- **The two ceilings:** the binding depth is below both, is one of the two, and is the geometric one or the thrust one according to which is smaller, with the saving following the binding depth (`t53_binding_below_both`, `t54_binding_is_one_of_them`, `t55_geometry_binds`, `t56_thrust_binds`, `t57_saving_at_binding`).
- **The optimum is a supremum:** Reading B and therefore the mass ratio fall as the exhaust velocity rises, while availability requires Reading A strictly below the body's address, so the optimum is approached at the open endpoint and not attained (`t58_reading_b_falls_with_target`, `t59_mass_ratio_falls`, `t60_optimum_is_a_supremum`).
- **Each body prescribes its own engine:** the prescription is the body's address carried to specific impulse, is nonnegative, and rises with compactness (`t61_prescription_is_the_address`, `t62_prescription_nonneg`, `t63_compact_prescribes_higher`).
- The vehicle mass a thrust supports meets the floor exactly, rises with thrust and falls with the floor (`t64_supported_meets_floor`, `t65_more_thrust_more_mass`, `t66_higher_floor_less_mass`).
- **A vehicle meeting the floor cannot lift itself:** a thrust per unit mass below the surface gravitational acceleration gives a thrust-to-weight below one and a net downward force at rest on the surface, and a thrust-to-weight below one half is below one (`t67_cannot_launch`, `t68_half_is_below_one`).
- **The placement carries the body and the drive only**, the matched radius in meters being the Schwarzschild radius times the matched ratio, with no vehicle mass entering it; and the propellant a vehicle carries is a strict fraction of its mass (`t69_placement_from_body_and_drive`, `t70_propellant_mass`).
- All of the above close under one master theorem (`MASTER_burn_depth_and_thrust_floor`).

### Issue 9, Article 7 · Fatigue Is Loss of Damping Capacity: the Endurance Limit as a Damage–Recovery Balance, the Basquin Exponent Identified, and Why the Knee Is Sharp

**Coordinate** \[9,9,2,53\](ENGR) · Identity Physics Series · Engineering Ground, Applied Structures  
**Published** ProofPress, Volume 1, Issue 9, Article 7 · https://proofpress.org/proofpressorg-fatigue-damping-loss  
**Verified** 100 theorems · 1,134 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_ForcedResponse_CyclesToShatter_Reduction.lean>

**Abstract.** **Fatigue is loss of damping capacity.** The quantity that falls under cyclic load is the damping ratio ζ, a measurable material property with its own instrumentation, and not an abstract damage variable. From that identification follow a closed-form endurance limit, the test for whether a material has one at all, the Basquin exponent identified as the exponent in a degradation law, and the sharpness of the knee as a consequence of that exponent rather than a separate fact. Static strength alone fixes the capacity the life law runs on, with no fitting.

This article reaches those results by descent, and the descent is short. The Dynamic Equation carries external forcing as a primitive term at Layer 0: d/dt (IM · Pv) = Σ λ_X · O_X · S + F_ext. Across the corpus, F_ext is realized the same way in every substrate — `f_ext_op s δ = { s with B := s.B + δ }` — and the theorem that it leaves Pattern, Narrative and Adaptation unchanged is carried in more than twenty files. This reduction states what that realization establishes, and then applies it repeatedly.

**External forcing is rank one.** The reachable set under F_ext alone is a line in a four-coordinate state: three of the four primitives are not externally reachable at all. Forcing moves torsion τ = B/P, so it carries a system across every phase boundary, while Pattern capacity is invariant under every external event. **All structural change is endogenous**; the outside sets conditions and nothing else. A control engineer reads the same statement as underactuation by three.

**Pure forcing has no memory.** F_ext is additive — δ₁ then δ₂ lands exactly where δ₁+δ₂ lands in one application, with no trace of the sequence. Therefore **a system that survives a load once survives it indefinitely under forcing alone**, and cyclic damage cannot be externally caused. Whatever accumulates accumulates in Σ λ_X · O_X.

That places damage in the Behavior-to-Pattern coupling, and the Tacoma–Scanlan reduction \[9,9,2,52\] says what Pattern is made of in a loaded structure: **P = 2Iζ**, inertia times damping. So **fatigue is loss of damping capacity**, and the quantity that falls under cyclic load is a measurable material property rather than an abstraction. Writing degradation per cycle as dP/dN = −k·B^m and shatter at P = B/TL gives N_f = (P₀ − B/TL)/(k·B^m), which for loads well below static strength is **N_f ∝ B^−m** — the Basquin form, with the empirical fatigue exponent identified as the exponent in the pattern-degradation law.

**The endurance limit is a balance.** Adding the restoring action of the internal operators, dP/dN = −k·B^m + r, gives a load at which degradation and recovery cancel exactly: **B_e = (r/k)^(1/m)**. The balance condition is identical whether damage is additive or multiplicative, since the P factor cancels, so the result does not depend on the form of the damage law. An endurance limit therefore exists exactly when the substrate carries a stress-independent recovery channel, and the stress-independence is forced rather than assumed: **dissipation is driven and scales with load, while conservative relaxation is a function of configuration and cannot.** Against published data this places 1045 steel's plateau at 0.500 × static and 2024-T4 aluminum's reference ratio at 0.350 × static, both inside Locked, and the condition separates them correctly: steel carries the channel and has a limit, aluminum does not and has none. It reproduces the accepted metallurgical account of the fatigue limit as a balance between fatigue damage and localized strengthening.

**The knee is sharp because the exponent is large.** The damage-to-recovery ratio is (B/B_e)^m, so at m = 8.696 a ten percent overload raises damage over recovery by 2.291× and a doubled load by 414.7×. Sharpness is a consequence of m, not a separate fact.

Two further results follow. **The existence of fatigue proves Pattern is controllable**: damage is a nonzero B→P coupling, which is exactly the first-order reachability condition that Round-one underactuation leaves open, so damage and the control channel are one coupling read with two signs — which is why cyclic loading both degrades and strengthens metals. And the lossless boundary already carried in forty-one corpus files, `F_ext > A · P · B`, is the endurance condition in its corpus form, giving **A · B = (B_e/static) · TL**, which a fatigue test reads off directly: 0.068449549992008 for 1045 steel and 0.0479146849944056 for 2024-T4.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_ForcedResponse_CyclesToShatter_Reduction.lean` at coordinate \[9,9,2,53\](ENGR), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the anchor as ten Torsion Limits, the bare term as one thousand of them, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the multiplier factoring as 7 · 11 · 13, the one-step anchor route Ω₀ × 100.1, the Torsion Limit positive, and the corridor floor in closed form, positive and below the ceiling (`t1_anchor_is_ten_tl`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_multiplier_factors`, `t6_anchor_route`, `t7_tl_pos`, `t8_tl_iva_value`, `t9_iva_floor_below_limit`, `t10_tl_iva_pos`).
2. The phase structure on torsion τ = B/P: zero Behavior is Noble, Noble and Shatter are exclusive, Locked and IVA are exclusive, IVA and Shatter are exclusive, the reading is a function of the ratio alone, and **the four phases exhaust every non-negative reading** (`t11_zero_behavior_is_noble`, `t12_noble_shatter_exclusive`, `t13_locked_iva_exclusive`, `t14_iva_shatter_exclusive`, `t15_phase_is_ratio_only`, `t16_phases_exhaust`).
3. **The intervention theorem.** External forcing leaves Pattern, Narrative and Adaptation unchanged and moves Behavior by addition, stated termwise and then as one statement (`t17_f_ext_preserves_p`, `t18_f_ext_preserves_n`, `t19_f_ext_preserves_a`, `t20_f_ext_on_b`, `t21_intervention`).
4. **The reachable set under forcing is exactly the Behavior line, in both directions:** a state is reached from `s` if and only if it agrees with `s` off Behavior, and **Pattern capacity is invariant under every external event** (`t22_reachable_set_is_a_line`, `t23_pattern_invariant_under_all_forcing`).
5. Forcing still carries a system across every boundary: positive forcing raises torsion, negative lowers it, **for any state with positive Pattern there is a forcing that puts it in Shatter**, and that state has the Pattern capacity it started with — **phase changes without Pattern changing** (`t24_positive_forcing_raises_torsion`, `t25_negative_forcing_lowers_torsion`, `t26_forcing_reaches_shatter`, `t27_phase_change_without_pattern_change`).
6. **All structural change is endogenous.** Any difference in Pattern, Narrative or Adaptation between two states rules out forcing as its cause (`t28_structural_change_is_endogenous`).
7. **Pure forcing has no memory.** Forcing composes additively and commutes, zero forcing is the identity, and **n applications of δ land exactly where one application of n·δ lands**, proved by induction on n (`t29_forcing_additive`, `t30_forcing_commutes`, `t31_zero_forcing_identity`, `t32_no_memory`).
8. **Nothing accumulates:** the torsion reading after any number of applications is the closed linear form (B + n·δ)/P, and **a strict drop in Pattern capacity is unreachable by any number of external events whatsoever** — cyclic damage is internal, as a consequence rather than a premise (`t33_nothing_accumulates`, `t34_cyclic_damage_is_internal`).
9. **The forcing domain is a statement about the substrate.** Under the guard that Behavior stays positive, Behavior cannot be driven to zero and **Noble cannot be imposed from outside**; without the guard, Noble is reached. The guard is automatic above zero (`t35_guarded_excludes_zero_behavior`, `t36_noble_not_externally_reachable`, `t37_unguarded_reaches_noble`, `t38_guard_automatic_above_zero`).
10. **Pattern capacity in a driven structure is inertia times damping.** The driven ratio is torsion on that reading, **onset at ratio one is exactly torsion at the Torsion Limit** as a biconditional, raising damping lowers the ratio, and the capacity is positive (`t39_driven_ratio_is_torsion`, `t40_onset_is_limit`, `t41_damping_lowers_ratio`, `t44_pattern_of_damping_pos`).
11. **Fatigue is loss of damping capacity.** At fixed inertia a fall in damping is exactly a fall in Pattern capacity, and losing damping drives the ratio toward onset (`t42_fatigue_is_damping_loss`, `t43_damping_loss_climbs_toward_onset`).
12. **Pattern capacity from static strength, with no fitting:** static strength is the Torsion Limit times Pattern capacity, **a state loaded at static strength sits exactly at the Shatter boundary**, and the capacity is positive and strictly increasing in strength (`t45_static_strength_from_capacity`, `t46_static_load_is_shatter_boundary`, `t47_pattern_capacity_pos`, `t48_pattern_capacity_mono`).
13. **The life law.** Cycles to shatter times the loss per cycle is exactly the capacity available above the shatter load, life is positive below static strength, **the Basquin form holds as the load-power identity**, and raising the load lowers the available capacity (`t49_life_law`, `t50_life_pos_below_static`, `t51_basquin_form`, `t52_available_capacity_decreasing`).
14. The published slopes give the exponent by reciprocal for both materials, and **the exponent is a substrate response and is not set by the structure: the life law closes for every exponent whatsoever** (`t53_steel_exponent`, `t54_aluminum_exponent`, `t55_exponent_is_substrate_response`).
15. **The endurance limit is a balance.** Net degradation is zero at B_e = (r/k)^(1/m), **recovery dominates strictly below it** and **damage dominates strictly above it**, the limit is positive, and it rises with the recovery rate (`t56_endurance_balance`, `t57_below_endurance_recovers`, `t58_above_endurance_damages`, `t61_endurance_limit_pos`, `t62_endurance_rises_with_recovery`).
16. **The balance is invariant under the form of the damage law:** with damage and recovery both proportional to Pattern capacity the Pattern factor cancels from both sides, so additive and multiplicative damage give the same balance condition (`t59_balance_invariant_under_damage_form`).
17. **An endurance limit exists exactly when a stress-independent recovery channel exists**, as a biconditional on the positivity of r (`t60_endurance_exists_iff_recovery`).
18. **The endurance readings on the torsion scale.** 1045 steel at 0.500 × TL and 2024-T4 aluminum at 0.350 × TL, computed exactly; **both lie strictly inside Locked**; any ratio below the corridor floor is a Locked reading; and **the scale is shared, since the ratio is recovered from the reading for any material whatsoever** (`t63_steel_tau_endurance`, `t64_aluminum_tau_endurance`, `t65_both_inside_locked`, `t66_ratio_below_floor_is_locked`, `t67_scale_is_shared`).
19. **The knee, and why it is sharp.** The damage-to-recovery ratio is one at the limit, below one beneath it, above one past it, multiplicative in the load ratio, positive, and **strictly increasing in the exponent** — so sharpness follows from the exponent rather than standing beside it (`t68_knee_at_one`, `t69_knee_below_one`, `t70_knee_above_one`, `t71_sharpness_from_exponent`, `t72_knee_multiplicative`, `t73_knee_pos`).
20. **The lossy boundary in its corpus form.** Lossless absorption and the lossy condition are mutually exclusive and exhaustive, **the boundary evaluated at the endurance limit gives A · B = (B_e/static) · TL**, the two materials' products are computed from their published strengths in MPa, and **the product is what a fatigue curve supplies — every factorization closes, so A and B are not separately fixed by it** (`t74_dominance_lossy_exclusive`, `t75_dominance_lossy_exhaust`, `t76_ab_product`, `t77_ab_steel`, `t78_ab_aluminum`, `t79_product_not_factors`).
21. **The existence of fatigue proves Pattern is controllable.** A strict drop in Pattern under positive Behavior requires a nonzero coupling, and **a nonzero coupling makes any target Pattern value reachable by one forcing followed by the coupling** (`t80_fatigue_is_nonzero_coupling`, `t81_pattern_controllable`).
22. **One channel, two signs.** The same coupling with opposite sign raises Pattern by exactly as much as it lowers it, and under positive Behavior a positive coupling raises Pattern while a negative one lowers it — **work hardening and fatigue are the same channel** (`t82_one_channel_two_signs`, `t83_hardening_and_fatigue`).
23. **The Lagrangian projection places every operator but the Behavior operator at the identity.** The Lagrangian is the kinetic product less the potential sum, the potential is symmetric and additive, **forcing enters the potential by addition alone**, the Euler–Lagrange content is Narrative momentum against the Pattern–Behavior balance, and **the three independent routes — forcing, projection and damage coupling — meet on the Behavior axis** (`t84_projection_identity_off_b`, `t85_lag_total_form`, `t86_potential_symmetric`, `t87_potential_additive`, `t88_forcing_in_potential`, `t89_el_balance`, `t90_three_routes_meet_on_b`).
24. **The cyclic companion to the static onset.** Any strictly falling damping sequence drives the driven ratio strictly up, **onset is reached at the critical damping B/(2I)**, the structure starts below onset exactly when damping exceeds that value, and **the static and cyclic cases share one threshold** (`t91_cyclic_approach_to_onset`, `t92_onset_damping`, `t93_below_onset_iff_damping_above`, `t94_one_threshold`).
25. **The e-fold reading of the multiplicative form:** zero at the shatter load, strictly positive below it, **additive along a path**, and strictly decreasing in the load (`t95_efolds_zero_at_shatter`, `t96_efolds_pos_below_shatter`, `t97_efolds_additive`, `t98_efolds_decreasing`).
26. **The IVA corridor on load is the band between 88% and 100% of static strength**, and it is nonempty for every positive static strength (`t99_corridor_on_load`, `t100_corridor_nonempty`).
27. The master theorem gathers the anchor, the intervention theorem, the reachable set, additivity, the internality of cyclic damage, fatigue as damping loss, Pattern capacity from static strength, the life law, the endurance balance with its existence condition and its invariance under the damage form, the knee at the limit and its sharpening with the exponent, the two torsion-scale readings, controllability with the two-sign channel, and the Lagrangian projection, into one conjunction (`MASTER_forced_response_cycles_to_shatter`).

**What the formal layer does not carry.**Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The published fatigue constants themselves — σ'_f, b, UTS and the endurance ratios for 1045 steel and 2024-T4 — are handbook values a reader supplies from a materials data set; the formal layer carries the exponent relation they feed, the torsion-scale placements they produce and the bounds those are read against. The cycle counts of §14 are the life law evaluated at a stated anchoring convention, and the formal layer carries the law, the band and the corridor placement rather than any particular convention's numbers. And the 8.9% systematic exponent drift that separates the two damage laws in §13 is a numerical comparison of two closed forms the formal layer does carry, over a stress range a reader chooses.

### Issue 9, Article 8 · Every Power-Limited Drive Is One Relation: a · α · v_e = 2, the Specific-Mass Decomposition, the Radiator–Core Crossover at 749.54 K, and the Matched Radius as the Drive's Impedance Match

**Coordinate** \[9,9,2,54\](ENGR) · Identity Physics Series · Engineering Ground, Propulsion  
**Published** ProofPress, Volume 1, Issue 9, Article 8 · https://proofpress.org/proofpressorg-power-limited-drive  
**Verified** 116 theorems · 1,185 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_PowerLimitedDrive_Reduction.lean>

**Abstract.** A power-limited jet produces thrust F = 2P/v_e, and a power plant of specific mass α = m/P therefore delivers acceleration a = 2/(αv_e). The three quantities carry a fixed product:

> **a · α · v_e = 2**

Every electric, nuclear-electric, fusion-electric and photon concept is a row in that one relation, and the photon drive is its v_e = c endpoint — exhaust torsion exactly 1, which sits above the Shatter ceiling by exactly **1/TL = b₀² = 7.304649921853084**, the square of the geometric base. Having no mass ratio to trade, the photon drive's entire design problem collapses to a = 2/(αc).

Specific mass itself decomposes. A core scaling with thermal power, conversion hardware scaling with electric power, and a radiator scaling with waste heat over the fourth power of rejection temperature give α = k_core/η + k_conv + k_rad(1 − η)/(ηT_c⁴). Minimizing radiator mass against the Carnot bound fixes the cold-to-hot temperature ratio at **T_c/T_h = 3/4** and the conversion efficiency at **η = 1/4** exactly, independent of every material property and of T_h, where the waste-heat multiplier (1 − η)/η is exactly **3**. At that efficiency

> **α = 4k_core + k_conv + 3k_rad/T_c⁴**

and **only one of the three addends carries the rejection temperature.** Every materials advance acts on that one term and leaves the others untouched, so α descends to the energy-density floor 4k_core + k_conv and the dominant term exchanges identity at a computable crossover. For a core of 0.493 kg/kW_th and the specification below, the crossover is **T_c = 749.54156 K**. Flown and studied high-power radiators run 375–550 K, which places every one of them on the radiator-dominated side by factors of 3.4 to 16.

Specific mass and mission duration prescribe the exhaust velocity, v_e(opt) = κ√(2t/α) with κ ∈ [0.60, 0.97]. Requiring the prescribed exhaust torsion to land in the IVA corridor gives a two-sided condition on α whose width is exact rational arithmetic, **α_hi/α_lo = (TL/TL_IVA)² = 625/484 = 29.1322314%**, independent of mission duration, of κ, and of every material property.

The matched radius acquires an operational reading. Since r_match = r_s/τ_A² and r_s = 2GM/c²,

> **v_esc(r_match) = τ_A · c = v_e**

so the matched radius is the shell where local escape speed equals exhaust speed. A vehicle in free fall from rest at infinity arrives there moving at exactly its own exhaust velocity, which is the condition under which propulsive efficiency is exactly 1 — the exhaust is left at rest and carries away no kinetic energy. The shell lies outside a body exactly when **τ_A < √(r_s/R_body)**.

Reading A and Reading B separate as a power series in the conversion fraction:

> **(τ_B − τ_A)/τ_A = Σ (2η)ⁿ/(2n+1) = 2η/3 + 4η²/5 + 8η³/7 + ⋯**

so a velocity budget is exact to 1.16 parts per million at the worked specification, to 0.49% at the corridor floor, and to 0.63% at the Shatter ceiling.

Constant-thrust flight has a closed form. Writing T₀ = m_dry/ṁ for the dry-mass burn time and u = Δv/v_e, elapsed time is t = T₀(e^u − 1) and distance is s = v_e T₀(e^u − 1 − u), so that

> **s = v_e · t − T₀ · Δv** exactly.

A complete specification follows from published parts: a 1,000 kW_th core at 493 kg, conversion at the rejection optimum, 23.717 m² of radiator at a 900 K cold side, dry mass 1,230 kg, α = 4.921 kg/kW_e, Isp 56,929 s, T₀ = 24.2966 years, 448.932 km/s over a 30-year burn, and 1,232.17 AU of reach. A Pluto orbiter arrives in 5.855 years at a mass ratio of 1.2555, and the solar gravitational lens focus at 549 AU in 24.50 years at 2.26255. **The 30-year reach is nearly independent of specific mass** — a factor of 1.856 in α moves it only from 1,179.62 to 1,250.30 AU, a factor of 1.060. Thrust is 0.895597 N, which is short of Mars surface weight by at least 5,110×, so the architecture is prescribed rather than chosen: built in space, never landing. A secondary drive is priced leg-by-leg through the mass-ratio gate, and the gate admits only a fusion-class secondary — 100 km/s costs 1.2023× in mass ratio to carry a twentieth of the rapidity where 9 km/s costs 11.633×.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_PowerLimitedDrive_Reduction.lean` at coordinate \[9,9,2,54\](ENGR), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the Torsion Limit as the anchor over ten, the bare term as one thousand Torsion Limits, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the one-step anchor route Ω₀ × 100.1, the multiplier factoring as 7 · 11 · 13, the Torsion Limit positive and lying strictly inside the unit interval, the corridor floor in closed form, positive and below the ceiling, the corridor as the band from 0.88 TL up to TL, the speed of light positive, and **the Torsion Limit and its landing as exact rationals** (`t1_tl_value`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_anchor_route`, `t6_multiplier_factors`, `t7_tl_pos`, `t8_tl_iva_value`, `t9_floor_pos_below`, `t10_tl_in_unit`, `t11_tl_rational`, `t12_landing_rational`, `t13_c_pos`, `t14_corridor_band`).
2. The phase structure on a torsion reading: zero is Noble, the corridor floor is IVA, the Torsion Limit is Shatter, any reading inside the corridor is IVA, any reading at or above the limit is Shatter, and any reading strictly below the floor is Locked (`t15_zero_is_noble`, `t16_floor_is_iva`, `t17_limit_is_shatter`, `t18_corridor_is_iva`, `t19_above_limit_is_shatter`, `t20_below_floor_is_locked`).
3. **One relation covers every power-limited drive.** Reading A is the speed over the limiting speed; jet power and thrust give **F = 2P/v_e** identically; and a plant of specific mass α delivers an acceleration whose product with α and the exhaust velocity is **exactly 2**, stated both as the fixed product and in its acceleration form, with acceleration as thrust over mass carrying the plant's own mass. **Specific power factors as 1/α = (c/2) · a · τ_A**, an acceleration times an exhaust torsion, and also as half the acceleration times the exhaust velocity. Acceleration is positive for a positive plant and drive, and falls as either of the other two quantities rises (`t21_reading_a`, `t22_thrust_from_power`, `t23_fixed_product`, `t24_accel_form`, `t25_accel_is_thrust_over_mass`, `t26_spec_power_form`, `t27_spec_power_operator`, `t28_accel_pos`, `t29_accel_antitone`, `t30_accel_antitone_in_alpha`).
4. **The photon drive is that relation's endpoint.** The geometric base is positive and its square is the landing; **the photon exhaust torsion is exactly one**; it stands above the Shatter ceiling by **exactly the squared geometric base**, equivalently by the exact rational 62500000000000/8556193749001; its acceleration depends on specific mass alone; the inverse solve returns the specific mass a target acceleration requires; and that torsion classifies as Shatter (`t31_b0_pos`, `t32_b0_sq`, `t33_photon_torsion`, `t34_photon_over_ceiling`, `t35_photon_factor_rational`, `t36_photon_accel`, `t37_photon_inverse`, `t38_photon_is_shatter`).
5. **The cooling capacity of a drive's own propellant.** The sink ratio is **2Δh/v_e² with the power cancelling entirely**, mass flow is twice the power over the squared exhaust velocity, the ratio is positive for a positive enthalpy rise and falls as the square of the exhaust velocity, the crossover squares to twice the enthalpy rise, the propellant carries **exactly the whole jet power at the crossover**, and less than it above (`t39_sink_power_free`, `t40_mass_flow`, `t41_sink_pos`, `t42_sink_antitone`, `t43_crossover_sq`, `t44_at_crossover`, `t45_above_crossover`).
6. **The rejection optimum, settled without derivatives.** The deficit from 27/256 **factors as (4x − 3)²(16x² + 8x + 3)/256**, whose cofactor is a shifted square and therefore positive; together these give the optimum value, the global maximum, and **its attainment only at three quarters**. Hence the radiator-optimal efficiency is **exactly one quarter**, the waste-heat multiplier there is **exactly three**, and the minimized radiator mass is proportional to **256/27**. The multiplier is positive on the unit interval, antitone in efficiency, and equal to the reciprocal efficiency less one; the deficit vanishes only at the optimum (`t46_rej_factorization`, `t47_cofactor_pos`, `t48_rej_at_opt`, `t49_rej_le_opt`, `t50_rej_unique`, `t51_eta_optimal`, `t52_multiplier_three`, `t53_min_radiator`, `t54_multiplier_pos`, `t55_multiplier_antitone`, `t56_multiplier_form`, `t57_deficit_zero_iff`, `t58_optimum_pair`).
7. **Specific mass decomposes, and exactly one addend carries the temperature.** At quarter efficiency the three-addend form reduces to 4k_core + k_conv + 3k_rad/T_c⁴, which separates into the energy-density floor plus a single temperature-carrying addend; the floor is independent of the rejection temperature; specific mass descends strictly toward it as the cold side rises; and the floor is a strict lower bound wherever the radiator term is positive (`t59_alpha_at_opt`, `t60_one_addend_carries_T`, `t61_floor_T_free`, `t62_descends_to_floor`, `t63_floor_is_bound`).
8. **The crossover temperature in closed form.** The fourth root, carried as two square roots, returns its argument when raised to the fourth and is positive on positives; the crossover is positive, **satisfies the radiator-equals-core balance exactly**, places specific mass at eight core terms plus conversion, and **is the unique positive temperature at which the two addends agree**; below it the radiator addend dominates and above it the core addend does (`t64_fourth_root_pow`, `t65_fourth_root_pos`, `t66_crossover_pos`, `t67_crossover`, `t68_alpha_at_crossover`, `t69_crossover_unique`, `t70_radiator_dominates`, `t71_core_dominates`).
9. **The governing inequality and its exact width.** The band width is the **exact rational 625/484**, the upper edge is the lower edge times that rational, and **the width carries no dependence on mission duration or on the optimality coefficient**; both edges are positive and ordered; at the lower edge the prescribed torsion squares to the ceiling and at the upper edge to the floor; the prescribed torsion falls as specific mass rises; and the characteristic velocity squares to twice the duration over specific mass, which delivers the torsion from it (`t72_band_width`, `t73_edges_ratio`, `t74_width_parameter_free`, `t75_edges_pos`, `t76_edges_ordered`, `t77_at_lower_edge`, `t78_at_upper_edge`, `t79_torsion_antitone`, `t80_v_ch_sq`, `t81_torsion_from_v_ch`, `t82_band`).
10. **The matched radius is the drive's impedance match.** The propulsive-efficiency denominator is positive and **the deficit factors as (1 − r)²/(1 + r²)**, so efficiency is **exactly one at matched speed**, never exceeds one, and **attains one at matched speed and nowhere else**. The matched radius carries the torsion out of the ratio, the attracting mass cancels, **the squared escape speed at that shell is the squared exhaust speed**, the matched ratio is the squared reciprocal of Reading A, the shell lies outside a body **exactly when the squared torsion is below the compactness**, and the matched ratio is antitone on the positive side (`t83_prop_denom_pos`, `t84_prop_deficit`, `t85_prop_eff_one`, `t86_prop_eff_le_one`, `t87_prop_eff_unique`, `t88_matched_radius_form`, `t89_mass_cancels`, `t90_escape_is_exhaust`, `t91_matched_ratio_form`, `t92_compactness_gate`, `t93_matched_ratio_antitone`).
11. **The conversion fraction and the separation of the readings.** Reading A squared is twice the conversion fraction, which is non-negative; **the series convergence condition is Reading A's own domain**, stated as an equivalence; the leading term is carried; the Doppler factor is positive inside the unit interval and squares to the ratio itself; the separation is Reading B over Reading A less one; and Noble places the Doppler factor at one with Reading B and the conversion fraction at zero (`t94_tau_sq_is_twice_eta`, `t95_eta_nonneg`, `t96_convergence_condition`, `t97_leading_term`, `t98_doppler_pos`, `t99_doppler_sq`, `t100_separation_form`, `t101_noble`).
12. **The trajectory has a closed form.** Elapsed time and distance are the first- and second-order remainders of the exponential in the burn argument, so **the distance is the exhaust velocity times the elapsed time less the dry-mass burn time times the velocity gained**, and the two remainders differ by exactly that argument. A zero burn costs no time and covers no distance; both are positive for a positive burn; elapsed time is strictly increasing in the argument; the mass ratio is recovered from the elapsed time as the exponential of the argument; and **the argument is Reading B over the exhaust torsion** (`t102_distance_identity`, `t103_remainder_structure`, `t104_zero_burn`, `t105_time_pos`, `t106_dist_pos`, `t107_time_mono`, `t108_mass_ratio`, `t109_argument_is_gate`, `t110_trajectory_pair`).
13. The environmental margin and multi-drive pricing: a cold environment costs no margin, the margin exceeds one for any warm environment and rises with it, the gate and the burn argument are the same object under the logarithm, **staged legs multiply their mass ratios while their Reading B counts add**, and a single drive carrying the whole count is the one-leg case (`t111_margin_at_zero`, `t112_margin_gt_one`, `t113_margin_mono`, `t114_gate_is_argument`, `t115_legs_multiply`, `t116_single_leg`).
14. The master theorem gathers the anchor arithmetic, the fixed product with thrust from power and specific power in operator form, the photon endpoint with its squared-base factor and its phase, the sink law with its crossover, the rejection optimum with its factorization and uniqueness and the multiplier of three, the decomposition with its single temperature-carrying addend and the crossover balance, the band width of 625/484 with both edges, the impedance match with the propulsive-efficiency deficit and the compactness gate, the conversion fraction with the convergence condition, the trajectory identity, and the margin and the legs, into one conjunction (`MASTER_power_limited_drive`).

**What the formal layer does not carry.**Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The engineering coefficients of §10 — core, balance-of-plant and radiator specific masses, the hot-side temperature, the emissivity and the optimality coefficient — are published figures a reader supplies, bracketed across three cases; the formal layer carries the relations they feed. The decimal evaluations throughout, including the crossover at 749.5415596 K, the mission ledger and the hybrid pricing, are evaluations of expressions the formal layer carries exactly, with the coefficients entering as parameters. And the separation of §9 is carried in the formal layer as its exact identity, its leading term and its convergence condition, with the summed series stated in this article.

### Issue 9, Article 9 · Earth has 63 Million Years Left at Perihelion Against 439 at Mean Flux Lean4 Pinned Formally Verified 0 Sorry 0 Free Parameters CI Green

**Coordinate** \[9,9,3,26\](COSM) · Identity Physics Series · Cosmology  
**Published** ProofPress, Volume 1, Issue 9, Article 9 · https://proofpress.org/proofpressorg-goldilocks-annulus  
**Verified** 109 theorems + master · 1,038 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_GoldilocksAnnulus_Reduction.lean>

**Abstract.** A planet's habitability is read today from a zone computed by climate models. This reduction derives the zone instead, from inverse-square geometry and the Torsion Limit, and finds it is two regions rather than one.

The inner edge of the published habitable zone is the runaway greenhouse, the condition in which a planet's ocean passes entirely to vapor. That is the boil, and \[9,9,8,10\] places the boil at τ = TL: water boils when its vapor pressure equals the ambient pressure holding it, which is τ = B/P with Behavior the vapor pressure and Pattern the ambient pressure. The identification of Shatter with the runaway greenhouse is therefore the same physical event on the same axis, and it fixes the Shatter anchor on stellar flux without a fitted parameter. Writing the reduced flux s = S/S_runaway, the four phases land directly: Shatter at s ≥ 1, the IVA corridor at 0.88 ≤ s < 1, Locked below, Noble at zero.

Because flux obeys the inverse-square law exactly, the corridor transfers to orbital radius as an annulus whose outer edge stands to its inner edge in the ratio **√(1/0.88) = √(25/22) = 1.0660035818**, a pure number carrying no stellar quantity — **the same proportion around every star in the universe**. For the Sun the annulus runs 0.980581 AU to 1.045303 AU, a shell 9.68 million kilometers thick, and Earth sits 30.00% of the way across it. The conservative published zone splits at the IVA floor into **85.6% Locked and 14.4% IVA** by flux, which is the same division \[9,9,8,10\] makes inside liquid water, where the liquid legacy names as one thing is two — water holding and water simmering.

A planet moves, so the flux swings over an orbit as 4es/(1−e²)², and the corridor is narrow. A planet holds its phase for a whole orbit exactly when **e·s/(1−e²)² < (1 − 0.88)/4 = 3/100**, one quarter of the corpus band width and nothing else. Across the NASA Exoplanet Archive's self-consistent table, **91.83% of planets with a measured eccentricity cross phase every orbit**, and the median crosses the corridor a hundred and two times over.

Structural Precognition \[9,9,1,0\] supplies the governing quantity. External forcing moves Behavior only, so U survives a push exactly when δ < P(TL − τ), and in the IVA band the margin is at most 0.12 · TL · P — maximum gain, minimum margin. On the insolation axis the margin is 1 − s and the orbital excursion is the push, giving the margin utilisation Ũ = [s/(1−e)² − s]/(1 − s). **Earth spends 85.6% of its entire margin at every perihelion**, against a best-of-field of 17.4% among terrestrial-scale survivors — a factor of 4.9 — and it is the only body in either catalogue that is both IVA-resident and phase-holding. Bounded uncertainty is a theorem rather than a practice: an estimate within ε certifies the placement when τ̂ + ε < TL, which returns a three-way verdict and separates a planet genuinely on the boundary from a measurement too coarse to place. Run on the archive's published insolation bars, 47 rows certify below Shatter, 851 certify at or above it, and **20 stand on the boundary** — and those 20 are the field's own shortlist of Earth-analog candidates, selected here by an inequality on an error bar.

A main-sequence star brightens, so the margin closes on a clock. Earth entered the IVA band **1,059 Myr ago** and carries **63 Myr** of perihelion margin against **439 Myr** at mean flux, a factor of 6.97 between evaluating the margin at the largest forcing and at the average one. It was Locked for the first 77% of its main-sequence history: LUCA, the Great Oxidation Event and complex eukaryotes all fall in Locked, while the Ediacaran and the Cambrian fall in IVA — matching the Evolution reduction's independent placement of LUCA as Locked and sustained Darwinian life in the IVA corridor, with the boundary set at 0.88 × the runaway-greenhouse flux and no biology among the inputs. IVA residence is **14.98% of a main-sequence lifetime** at Earth's own crossing and runs from **8.18% to 21.81%** across the track, so the 424 Myr the complex rung cost on Earth bounds the host star at **M ∈ [0.70, 1.657] M_☉** at Earth's crossing, inside an outer reading of 1.925 and an inner one of 1.300: cool stars carry unlimited time and insufficient ultraviolet, hot stars carry the ultraviolet and run out of time.

The stellar engine itself is the template. \[9,9,2,0\] places hydrogen-to-helium fusion at a conversion fraction of 0.711852%, **Locked, clearing the IVA floor by 1.94%** — the holding state, which is the stability that buys ten billion years — while hydrogen-to-iron sits **IVA at 78.54% up the band**, and an iron core is where a star ends.

The phase of a body is not a number but a field. One degree is one tick of TL/100 on either scale, so the band runs **361.15 K to 373.15 K** and is exactly 12 degrees wide, and the ruler places the marks while the ratio **r = p_vap(T)/p_ambient** places the substrate between them. Because the ratio carries the ambient pressure, the boil moves with the body: **water boils at 268 K on Mars and at 569 K on the surface of Venus**, while the corridor's width in inverse temperature stays at −(R/L) ln 0.88 and carries no pressure at all. Running the ratio through a column shows it is **largest at the surface**: it falls with altitude exactly when the lapse rate exceeds **g* = R T²/(L H)**, a threshold Earth, Venus, Mars and Titan all clear, and downward a hydrostatic water column passes water's critical pressure at **2.239 km**, where the axis terminates rather than the ratio reaching the band — which is why a vent at 400 °C under 250 bar does not boil. A column therefore carries the corridor only when its surface stands past it, and **Venus is that case, cooling through the IVA band at 36 km altitude.** Two published numbers per body, a surface temperature and a surface pressure, settle every candidate solvent at once: the table returns **methane and ethane Locked on Titan**, methane Locked on Triton and Pluto, and water Locked on Earth, Mars, Europa and Venus's cloud deck — recovering each body's known liquid without being told it. Placing measured growth ranges on the same ruler, **the IVA band is the hyperthermophile band**, with the limit of known life at 122 °C standing at 1.22 TL. LUCA is characterized as a hyperthermophile of hydrothermal systems, IVA on the temperature axis, while the planet's insolation at 3.8 Gyr placed it at s = 0.7215 and its bulk water at r ≈ 0.021, both Locked — so the origin condition reads as **a Locked planet carrying an IVA pocket**, the surface holding to supply the duration and the pocket carrying the corridor.

Finally the cosmic shoreline, published as I ∝ v_esc⁴, follows from the escape balance: with the atmosphere a fixed fraction of planet mass, **I = f v_esc⁴/(4πεGRT)**, and the fourth power is forced the moment T is an absolute clock. Substituting the dynamical time gives a second branch at v_esc⁵/R², so the shoreline carries two ceilings exactly as \[9,9,0,20\] carries two for burn depth. On Solar System data the fourth power separates cleanly with a factor of **2.19** of room once the two bodies the literature itself calls marginal are set aside, while the fifth does not separate at all. With the matched-radius identity v_esc(r_match) = τ_A·c, the shoreline reads **I ∝ c⁴τ_A⁴/(RT)** and the thrust floor of \[9,9,0,20\] reads **F/m ∝ c⁴τ_A⁴u³/(fGM)** — the same object, read from the two sides of one gravitational boundary.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_GoldilocksAnnulus_Reduction.lean` at coordinate \[9,9,3,26\](COSM), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the Torsion Limit as the anchor over ten, the bare term as one thousand Torsion Limits, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the one-step anchor route Ω₀ × 100.1, the multiplier factoring as 7 · 11 · 13, the Torsion Limit positive and strictly inside the unit interval, the corridor floor in closed form and positive below the ceiling, **the Torsion Limit and the floor fraction as exact rationals**, and the band width as exactly three twenty-fifths (`t1_tl_value`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_anchor_route`, `t6_multiplier_factors`, `t7_tl_pos`, `t8_tl_in_unit`, `t9_tl_iva_value`, `t10_floor_pos_below`, `t11_tl_rational`, `t12_floor_rational`, `t13_band_width`).
2. The phase structure on a torsion reading: zero is Noble, the floor is IVA, the limit is Shatter, any reading inside the corridor is IVA, any reading at or above the limit is Shatter, any positive reading below the floor is Locked, and the boundaries are ordered (`t14_zero_is_noble`, `t15_floor_is_iva`, `t16_limit_is_shatter`, `t17_corridor_is_iva`, `t18_above_limit_is_shatter`, `t19_below_floor_is_locked`, `t20_boundary_ordering`).
3. **The Shatter anchor on stellar flux is the runaway greenhouse.** At the runaway boundary the reduced flux is one and the torsion is the Torsion Limit; the IVA floor in reduced flux is the floor fraction itself; a reduced flux at or above one is Shatter, one in the band is IVA, and a positive one below the floor is Locked; the floor lands at 0.9152 for the published solar anchor; and torsion on the axis is monotone in the flux (`t21_anchor_is_one`, `t22_runaway_is_shatter`, `t23_floor_in_flux`, `t24_flux_phase_shatter`, `t25_flux_phase_iva`, `t26_flux_phase_locked`, `t27_iva_floor_solar`, `t28_tau_mono`).
4. **The annulus, and the cancellation that makes it portable.** The annulus ratio squares to 25/22, which is the reciprocal floor fraction; it is positive and exceeds one; each edge squares to its own flux ratio and both are positive for a positive luminosity; **the squared edge ratio is the reciprocal floor fraction with every stellar term cancelled**, equal to 25/22 and to the squared annulus ratio; the outer edge stands beyond the inner one and the width is positive; **two luminosities give the same ratio**, and **relocating the anchor leaves the ratio unchanged** (`t29_ratio_sq`, `t30_ratio_is_recip_floor`, `t31_ratio_pos`, `t32_ratio_gt_one`, `t33_d_in_sq`, `t34_d_out_sq`, `t35_edges_pos`, `t36_anchor_cancels`, `t37_squared_ratio_rational`, `t38_matches_annulus`, `t39_out_beyond_in`, `t40_width_pos`, `t41_same_for_every_star`, `t42_anchor_relocation`).
5. **The phase-holding criterion.** The hold constant is exactly three hundredths and is a quarter of the band width; **the swing is the difference of the two extreme fluxes**; it is positive for a positive eccentricity and flux, zero for a circular orbit, and rises with both eccentricity and flux; holding the phase is the hold-constant inequality, equivalently the crossing number below one (`t43_hold_const`, `t44_hold_is_quarter_band`, `t45_swing_identity`, `t46_swing_pos`, `t47_hold_criterion`, `t48_circular_holds`, `t49_swing_mono_in_e`, `t50_swing_mono_in_s`, `t52_crossing_lt_one`).
6. **Bounded uncertainty certifies.** An estimate within its bar certifies the placement, a certified-Shatter bar places the row at or above the limit, the two certifications exclude each other, a sharper bar certifies whatever a wider one did, a zero-width bar certifies exactly the sub-limit readings, and **a row is uncertified exactly when its bar spans the limit** (`t53_cert_sound`, `t54_cert_shatter_sound`, `t55_cert_exclusive`, `t56_sharper_bar`, `t57_zero_bar`, `t58_spanning`).
7. **The margin, and the minimum-margin band.** The margin is positive below Shatter and vanishes at it; **in the IVA band it is at most the band width**, and **it is the smallest of any sub-Shatter state**; the push is positive for a positive eccentricity and zero for a circular orbit; surviving perihelion is the push below the margin, equivalently the perihelion flux below Shatter; the utilisation is positive and **rises as the margin narrows**; and the push is the perihelion flux less the mean (`t59_margin_pos`, `t60_margin_zero`, `t61_iva_margin_bound`, `t62_iva_least_margin`, `t63_push_pos`, `t64_push_zero`, `t65_util_lt_one`, `t66_survives_iff`, `t67_util_pos`, `t68_util_antitone_in_margin`, `t69_push_form`).
8. **The clock.** The track is unity at the present and recovers the present flux; it rises with time and carries the flux up with it; **the margin closes as the flux rises**; the residence is positive, **falls as the star brightens**, and is therefore **a band rather than a point**; the main-sequence lifetime is positive and a heavier star lives a shorter life; and **a lighter host clears whatever rung a heavier one cleared** (`t70_track_now`, `t71_flux_now`, `t72_track_mono`, `t73_flux_mono`, `t74_margin_closes`, `t76_residence_pos`, `t77_residence_antitone`, `t78_residence_band`, `t80_lifetime_pos`, `t81_heavier_shorter`, `t83_lighter_clears`).
9. **The energy ladder.** The corridor is ordered, **the stellar engine is Locked below the floor** and clears it by a positive shortfall, **the iron peak sits inside the corridor**, annihilation stands above the ceiling, and the full ordering closes (`t84_ladder_ordered`, `t85_engine_locked`, `t86_iron_is_iva`, `t87_annihilation_shatter`, `t88_engine_shortfall`, `t89_ladder_full`).
10. **The ruler and the ratio.** One degree is the anchor over a thousand, one hundred ticks is the Torsion Limit, eighty-eight ticks is the floor, **the band is exactly twelve ticks wide**, and the Kelvin marks carry the same ticks; **at the boil the ratio is one and the torsion is the limit**; a ratio in the band is IVA and a zero ratio is Noble; and the ratio is **antitone in the ambient pressure** and monotone in the vapor pressure (`t90_tick_value`, `t91_hundred_ticks`, `t92_eightyeight_ticks`, `t93_band_twelve_ticks`, `t94_kelvin_marks`, `t95_boil_is_shatter`, `t96_ratio_iva`, `t97_ratio_noble`, `t98_ratio_antitone`, `t99_ratio_mono`).
11. **The column and the critical point.** The threshold is positive, and **the ratio falls with altitude exactly above it**; above the critical pressure the axis terminates; hydrostatic pressure rises with depth, the terminating depth carries the pressure to critical exactly, and **below that depth no boil exists** (`t100_gstar_pos`, `t101_falls_iff`, `t102_axis_terminates`, `t104_hydro_mono`, `t106_z_term`, `t107_below_terminate`).
12. **The shoreline's two branches.** The fourth-power branch solves the escape balance and carries a radius and a time; the dynamical time is positive, and **substituting it carries the fourth power into the fifth**; the two branches differ by one power of the escape velocity; the shoreline group rises as the fourth power of that velocity; and **the matched-radius identity carries Reading A onto an escape velocity**, so the shoreline is a fourth power of Reading A (`t108_shore4_solves`, `t109_shore4_form`, `t110_tdyn_pos`, `t111_shore5_from_tdyn`, `t112_branches_differ`, `t113_quartic`, `t114_reading_a_of_escape`, `t115_shoreline_on_reading_a`).
13. The master theorem gathers the anchor arithmetic, the annulus with its cancellation and its exact rational, the hold constant as a quarter of the band width, bounded-uncertainty certification, the margin with the IVA bound, the residence antitone in luminosity, the ladder with the engine Locked and the iron peak IVA, the twelve-tick band, and the shoreline balance, into one conjunction (`MASTER_goldilocks_annulus`).

**What the formal layer does not carry.**Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The published boundaries — the runaway greenhouse at 1.04, the maximum greenhouse at 0.35, the K5 ultraviolet threshold, the Gough track's coefficients and the mass–lifetime exponent — are figures a reader supplies, and the formal layer carries the relations they feed. The decimal evaluations throughout, including the Sun's annulus in astronomical units, Earth's four band-crossing dates, the residence percentages and the host-mass window, are evaluations of expressions the formal layer carries exactly, with the published figures entering as parameters. And the catalogue runs of §5, §6, §11 and §12 are counts over published rows, with the inequalities they apply carried here as theorems.

### Issue 9, Article 10 · Mars Needs 46.8 Kelvin and 101 Worlds Are Placed in the Terraformable Band Lean4 Pinned Formally Verified 0 Sorry 0 Free Parameters CI Green

**Coordinate** \[9,9,3,28\](COSM) · Identity Physics Series · Cosmology  
**Published** ProofPress, Volume 1, Issue 9, Article 10 · https://proofpress.org/proofpressorg-terraformable-band  
**Verified** 50 theorems + master · 551 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_TerraformableBand_Reduction.lean>

**Abstract.** The Goldilocks annulus of \[9,9,3,26\] places a planet between the boil at τ = TL and the IVA floor at τ = 0.88 × TL. A planet already inside that annulus is reading IVA. A planet inside the boil is reading Shatter. **Locked is the one phase with headroom**, and this reduction gives the band inside Locked where that headroom can be spent.

Three results follow, and each is stated against the published record.

**The brightening law runs on fractional main-sequence age.** Writing f = age / t_MS and normalizing the Gough 1981 solar track to zero-age main sequence gives **L(f)/L_zams = 1.4 / (1.4 − (400/457) f)** — one law, every stellar mass, no free parameters, and the substitution is a change of variable that maps the Gough denominator term for term rather than approximating it. Earth crosses s = 0.88 at f = 0.351138, which is **1,059 Myr ago**, the figure carried in \[9,9,3,26\]. The crossing has a closed form and needs no iteration.

**The far bound belongs to the working fluid.** The published outer edge of the habitable zone stands at effective flux 0.3853 for a Sun-like host under carbon dioxide and at 0.19 to 0.22 for an M8V host, and it moves with carbon dioxide partial pressure across the 1 to 35 bar range of the published parametrization. Engineered conductive aerosols warm per unit mass by a factor of 5 × 10³ over the best gases. Reduced, the near bound is geometric — s = 0.88 exactly, with luminosity, effective temperature and stellar radius all cancelling — and the far bound is a property of the forcing agent and the spectrum it sits under. The two bounds are different kinds of object, and the band between them is read accordingly.

**Required warming computes from luminosity and distance alone.** For a planet reading reduced flux s, the warming that carries it to the IVA floor is **ΔT = T_eq · [(0.88/s)^¼ − 1]**, with no interior model and no atmosphere model in it. Across the band the figure runs from 0.2 K to 74.9 K.

Applied to the NASA Exoplanet Archive, **101 planets** stand inside the band. Of the 47 whose host age and mass are both published, the star carries 31 of them to the IVA floor within its main sequence, and for 16 the main sequence closes first. Each route is certified across the published error bars: 35 of the 47 hold across the host age bar, 14 hold across all five bars taken at once, and ten of the forcing-route rows are certified.

Mars is carried from both directions. Run through the identical path with nothing specific to it, Mars reads s = 0.41417, stands **8.6%** across the band, requires **46.8 K**, and returns a retention figure **10.6×** worse than Earth's from mass and radius alone. The Sun reaches the IVA floor at Mars in 6.05 Gyr with about 5.4 Gyr of main sequence left. The published volatile inventory for Mars reaches about 7% of one bar against the tens of bars that near-ceiling forcing takes. Geometry and inventory are measured independently and they meet.

LHS 1140 b stands at **0.0865** across the band against Mars at 0.0857 and requires **46.7 K** against Mars at 46.8 K — the same placement to a tenth of a Kelvin, with an escape velocity of 20.13 km/s and a retention figure 24× better than Earth's, under a main sequence of 685 Gyr.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_TerraformableBand_Reduction.lean` at coordinate \[9,9,3,28\](COSM), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the Torsion Limit as the anchor over ten, the bare term as one thousand Torsion Limits, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the one-step anchor route Ω₀ × 100.1, the Torsion Limit positive and strictly inside the unit interval, the corridor floor in closed form and positive below the limit, and **the floor fraction as the exact rational 22/25** (`t1_tl_value`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_anchor_route`, `t6_tl_pos`, `t7_tl_in_unit`, `t8_tl_iva_value`, `t9_floor_pos_below`, `t10_floor_rational`, `t11_floor_in_unit`).
2. **Locked reads the same on either axis.** The floor in flux is the floor in torsion, and a body below the floor fraction in reduced flux is below the corridor floor in torsion, and conversely (`t12_floor_is_floor`, `t13_locked_iff`).
3. **The brightening track on fractional main-sequence age is the published track.** The coefficient is the Gough coefficient carried with the solar main-sequence lifetime and the solar reference age; **the two denominators are the same expression at every age**, so the rewrite is a change of variable; the tracks agree; the track reads one at zero-age main sequence, seven fifths at the solar fractional age with the coefficient returning two fifths exactly there, and the exact rational 3199/1199 at main-sequence close; the denominator and the track are positive across the main sequence; **the track rises with fractional age**; and a longer main sequence holds a body nearer zero-age (`t14_bright_c_route`, `t15_bright_c_bounds`, `t16_denominator_identity`, `t17_tracks_agree`, `t18_lrel_zams`, `t19_solar_point`, `t20_lrel_solar`, `t21_lrel_close`, `t22_denom_pos`, `t23_lrel_pos`, `t24_lrel_mono`, `t25_longer_ms_lower_f`).
4. **The band inside Locked.** A band member reads Locked; the band is nonempty exactly when the ceiling stands below the floor; the position reads zero at the ceiling and one at the floor, **rises with flux**, and lies in the unit interval across the band; **the floor carries no star and no agent in it**; **lowering a ceiling widens the band and leaves the floor where it stands**; and a body inside a higher ceiling stands inside a lower one (`t26_band_is_locked`, `t27_band_nonempty`, `t28_across_at_ceiling`, `t29_across_at_floor`, `t30_across_mono`, `t31_across_in_unit`, `t32_floor_carries_nothing`, `t33_lower_ceiling_widens`, `t34_ceiling_monotone`).
5. **Required warming.** The flux ratio reads one at the floor, **exceeds one strictly below it**, and **falls as present flux rises**; the warming factor carries the fourth power onto the flux ratio; and the required warming vanishes exactly at the floor (`t35_warmpow_at_floor`, `t36_warmpow_gt_one`, `t37_warmpow_antitone`, `t38_fourth_power`, `t39_no_warming_at_floor`).
6. **The route test.** The crossing expands to a line in fractional age; **a body standing at the floor crosses at its own present age**; the crossing rises with present fractional age and falls with present flux on the main sequence; the host route and the forcing route exclude each other; and a body at the floor inside its main sequence is host-delivered (`t40_ffloor_expand`, `t41_at_floor_crosses_now`, `t42_ffloor_mono_fn`, `t43_ffloor_antitone_s`, `t44_routes_exclude`, `t45_floor_body_delivered`).
7. **Certification across a published bar.** Certification is sound for the host route and for the forcing route by monotonicity, so **two endpoint evaluations settle the whole bar**; the two certifications exclude each other; a bar carrying both readings is characterised exactly as one standing on the boundary; and a zero-width bar certifies its own reading (`t46_cert_delivers_sound`, `t47_cert_forcing_sound`, `t48_certs_exclude`, `t49_boundary_characterised`, `t50_point_bar_certifies`).
8. The master theorem gathers the anchor arithmetic, Locked on either axis, the denominator identity and the track's values and monotonicity, the band position and the ceiling ordering, the required-warming readings, the floor-body crossing with the route exclusion, and both certification soundness results, into one conjunction (`MASTER_terraformable_band`).

**What the formal layer does not carry.** Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The published boundaries — the maximum-greenhouse outer edge at 1.611 AU and 1.67 AU for a Sun-like host and at effective flux 0.19 to 0.22 for an M8V host, the runaway and moist-greenhouse inner edges at 0.966 and 0.970 AU, the mass–lifetime exponent, the cosmic shoreline exponent and the Martian volatile inventory — are figures a reader supplies, and the formal layer carries the relations they feed. The decimal evaluations throughout, including Mars at 46.8 K and the band positions in Appendix A, are evaluations of expressions the formal layer carries exactly, with the published figures entering as parameters. And the catalogue run is a count over published rows, with the inequalities it applies carried here as theorems.

### Issue 9, Article 11 · Formally Verified Geometric Data for 5639 NASA Exoplanets Escape Velocity Surface Gravity Atmospheric Retention and Phase on Every Row Lean4 Pinned 0 Sorry 0 Axioms 0 Free Parameters CI Green

**Coordinate** \[9,9,3,29\](COSM) · Identity Physics Series · Cosmology  
**Published** ProofPress, Volume 1, Issue 9, Article 11 · https://proofpress.org/proofpressorg-geometric-completion  
**Verified** 61 theorems + master · 636 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_GeometricCompletion_Reduction.lean>

**Abstract.** The NASA Exoplanet Archive publishes 399 columns across 6,470 confirmed planets. Among them stand bulk density, insolation and equilibrium temperature. **Escape velocity, planetary surface gravity, atmospheric retention and phase are supplied here.**

This reduction carries them, together with their certification, from the constants of \[9,9,3,28\](COSM) and \[9,9,3,26\](COSM):

| column | rows carried |
|---|---|
| Escape velocity and surface gravity, Earth at 1 | **6,463** |
| Radius and mass resolved as a pair | **6,463** |
| Phase and torsion τ = TL · s | **5,642** |
| Atmospheric retention and the hold reading | **5,639** |
| Tankiness, where headroom carries the three-factor product | **586** |
| Overshoot past the Shatter limit | **5,053** |

Seven rows publish neither a mass nor a radius and are kept with the reason recorded. Every other row carries a reading, and every reading carries an interval.

Five results close the reduction, and each is stated against the published record.

**The density law carries both directions.** The interior density law ρ̄(x) = 4400 + 7400x³ at Earth's structural coordinate x = 0.53188 returns ρ̄ = 5513.4 kg/m³, so **R/R⊕ = (M/M⊕)^(1/3)** and **M/M⊕ = (R/R⊕)³**. The forward direction is the mass predictor of \[9,9,3,28\]; the reverse direction carries the radial-velocity half of the catalogue. On rows publishing both columns as determinations, inside the sub-boil gate and inside the law's range, the closure runs across **192 rows at 8.96% mean absolute error**, which carries the five-body figure of \[9,9,3,28\] onto a sample 38 times larger.

**Escape velocity reduces to radius exactly.** Under the closure, **v_esc/v_E = √(M/R) = √(R³/R) = R**, an identity with no approximation step, which is what supplies the escape-velocity column and collapses retention to **R⁴/I** on radius and insolation alone.

**The density law screens its own domain.** The law is a cubic in x over the unit interval, so its range is ρ̄ ∈ [4400, 11800] kg/m³, which restated in observable columns is **M/R³ ∈ [0.79806, 2.14024]**, adding no constant. It returns the standing Mars verdict at M/R³ = 0.71063. On the archive it reads 104 sub-boil mass cells above its range, and the archive's own limit flag stands on **60 of those 104 at 57.7% against a base rate of 3.5%, an enrichment of 16.6**.

**Phase is a reading of the flux axis.** Torsion on that axis is τ = TL · s, so the four phases of \[9,9,8,1\] §1.4 read directly off the band coordinate: **5,053 rows in Shatter, 573 in Locked, 16 in IVA Peak**. Geometry is carried in every phase, because phase names where a geometry stands under its F_ext rather than which geometry it is. The IVA Peak corridor runs 0.88 ≤ s < 1, twelve percent of the distance to the boil, and **the sixteen rows standing inside it each carry an s interval wider than the corridor**, with 49 further rows bracketing across it at a ratio of 3.06.

**The escape boundary is a level set of the retention column.** The cosmic shoreline stands at I ∝ v_esc⁴, and the level set of R⁴/I is that relation. Computed on thirteen solar system bodies with nothing fitted, retention orders **twelve of thirteen** into airless below and atmosphered above, with one crossing pair — Mars at 0.09456 and Ganymede at 0.09828, **3.93% apart**. Earth reads 1 by construction and stands **×10.373** above that crossing. Since the near bound is geometric, the band carries an insolation ceiling I ≤ (22/25) · S_RUN = 0.9152 S⊕, so **at R ≥ 1 R⊕, retention ≥ 1.0926573, a margin of ×11.3344**, and a critical radius of **0.545005 R⊕**.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_GeometricCompletion_Reduction.lean` at coordinate \[9,9,3,29\](COSM), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the Torsion Limit as the anchor over ten, the bare term as one thousand Torsion Limits, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the one-step anchor route Ω₀ × 100.1, the Torsion Limit positive and strictly inside the unit interval, the corridor floor in closed form and positive below the limit, **the floor fraction as the exact rational 22/25**, and the corridor width on the flux axis as 3/25 (`t1_tl_value`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_anchor_route`, `t6_multiplier_factors`, `t7_tl_pos`, `t8_tl_in_unit`, `t9_tl_iva_value`, `t10_floor_pos_below`, `t11_floor_rational`, `t12_corridor_width`).
2. **The interior density law and its range.** The law reads the mantle floor at zero and the ceiling at one, **rises with the structural coordinate**, and returns Earth's bulk density at Earth's coordinate; **its range over the unit interval is bounded at both ends**; that range divided by Earth's bulk density is **restated as a test on the two published columns, adding no constant**; and the reading that places Mars outside the solver's domain is returned by the same constant (`t13_rho_at_zero`, `t14_rho_at_one`, `t15_rho_mono`, `t16_rho_range`, `t17_rho_earth`, `t18_x_earth_in_unit`, `t19_codomain_screen`, `t20_mars_below_range`).
3. **The completion operator.** It rises with radius, is **injective on positive radii**, carries a positive radius to a positive mass, and a body it resolves **reads the density ratio at unity exactly**; the sub-boil gate in mass is bracketed as a ceiling in radius and the transfer from the ceiling to the gate is closed (`t21_mass_mono`, `t22_mass_inj`, `t23_mass_pos`, `t24_density_ratio_one`, `t25_gate_brackets`, `t26_gate_radius_cubes`, `t27_gate_transfer`).
4. **Escape velocity is radius.** Substituting the closure into the escape-velocity reading leaves radius, **with no approximation step**; the same substitution carries **surface gravity onto radius**; the two columns agree and both read one at Earth; and **retention reduces to the fourth power of radius over the insolation** (`t28_vesc_is_radius`, `t29_gsurf_is_radius`, `t30_vesc_eq_gsurf`, `t31_earth_unit`, `t32_retention_reduces`).
5. **The retention term.** It reads one at Earth, **rises with radius**, **falls as the insolation rises**, and **the legacy escape boundary is characterised exactly as a level set of it** (`t33_retention_earth`, `t34_retention_mono_R`, `t35_retention_anti_I`, `t36_level_set`).
6. **The products and the sign of the margin.** Earth's flux reading is the exact rational 25/26 and the shock denominator is 1/26; the shock margin reads one at Earth; **the sign of the margin carries the phase**, positive exactly below the limit; the overshoot is the same magnitude reflected and is positive past the limit; and both products read one at Earth and stay positive on a positive row (`t37_s_earth_rational`, `t38_shock_denominator`, `t39_shock_earth`, `t40_shock_sign`, `t41_shatter_is_reflected`, `t42_shatter_pos`, `t43_hold_earth`, `t44_tank_earth`, `t45_hold_pos`).
7. **The band carries its own retention floor.** The geometric near bound carries an **insolation ceiling of 572/625 exactly**, positive, with reciprocal **625/572**; a reading at or below the near bound stands below the ceiling; **retention inside the band at Earth radius and above is bounded below by that reciprocal**; the floor stands above the solar-system crossing **past eleven**; the critical radius at the ceiling is bracketed and the stated value stands inside the bracket; and **every body above it retains at the ceiling** (`t46_i_ceiling`, `t47_insolation_bound`, `t48_i_ceiling_pos`, `t49_floor_rational`, `t50_subsumption_bound`, `t51_margin_bound`, `t52_critical_radius`, `t53_r_crit_in_bracket`, `t54_above_crit_retains`).
8. **Phase on the flux axis, and certification.** The floor fraction carries the IVA floor onto the flux axis; **each occupied phase follows from its flux interval**; **every band reading is a Locked reading**; and certification on the retention reading is **sound by monotonicity in the insolation**, so one endpoint evaluation settles the whole published bar (`t55_floor_in_flux`, `t56_flux_shatter`, `t57_flux_iva`, `t58_flux_locked`, `t59_band_is_locked`, `t60_cert_retaining_sound`).
9. The master theorem gathers the closure, the escape-velocity identity, the reduction of retention to two observables, the retention floor and the phase into one conjunction (`t61_master`).

**What the formal layer does not carry.** Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The published figures — the cosmic shoreline exponent and its unconstrained zero point, the maximum-greenhouse far bounds, the solar-system masses, radii, insolations and atmosphere statuses, the bulk density of osmium, and the archive's own mass-basis and limit columns — are values a reader supplies, and the formal layer carries the relations they feed. The decimal evaluations throughout, including the crossing at 0.096402 and every row of the appendices, are evaluations of expressions the formal layer carries exactly. And the catalogue run is a count over published rows, with the inequalities it applies carried here as theorems.

### Issue 9, Article 12 · The Two Readings Across Substrates: Reading B as an E-Fold Count, the Square-Root Operator as a Constitutive Relation, and the Corridor in a Dielectric

**Coordinate** \[9,9,8,11\](MATH) · Identity Physics Series · Mathematics Ground, Foundations  
**Published** ProofPress, Volume 1, Issue 9, Article 12 · https://proofpress.org/proofpressorg-two-readings-substrates  
**Verified** 72 theorems · 910 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_TwoReadings_Substrate_Reduction.lean>

**Abstract.** The propulsion line from \[9,9,2,0\] through \[9,9,0,20\] carries two readings of one vehicle, and this reduction establishes which of them belong to propulsion and which belong to structure. **Reading B is an e-fold count.** Writing τ = ∫(−dY/Y) for a quantity Y consumed multiplicatively along a path parameter, the propellant exponent ln(m₀/m_f) is that integral for propellant mass along a burn, the optical depth ln(I₀/I) is the same integral for intensity along a slab, and the activity, charge and capital exponents are the same integral in their own substrates. All five solve dY/ds = −Y, so the consumed fraction is **1 − e^−τ** by solution rather than by resemblance, and τ = 2.3026 is one decade of attenuation in optics and a mass ratio of ten in propulsion — the same number carrying the same meaning. **Reading A transfers one level less widely**, requiring a substrate with a limiting speed, and a medium supplies one: the phase velocity is c/n, so v/c = 1/n, confined to (0,1] for n ≥ 1 by the same bound and the same reason that confines Reading A. **Reading A in a medium is the reciprocal refractive index**, and because ε_r = n² for a non-magnetic medium, the relative permittivity is 1/τ_A², which is the **matched ratio** — so the corridor's two matched radii, 53.357910481 and 68.902260435, are also the corridor's two permittivities, the same pair of numbers to thirty digits. The square-root torsion operator of \[9,9,0,17.1\] turns out not to be a corpus-internal device at all. **S is a constitutive relation**: n = √ε_r in optics, τ_surface = √C in gravitation, Z = √(μ/ε) in transmission, v = √(K/ρ) in acoustics — everywhere a characteristic speed or ratio is the square root of a ratio of two material or geometric properties. Its closure theorem matched_ratio(S X) = 1/X therefore instantiates physically and twice: in optics the matched ratio of a medium is the permittivity itself, and in gravitation the matched ratio of a drive tuned to a body's address is R/r_s, which places the matched radius exactly at the surface — the same statement as \[9,9,0,20\]'s address theorem, so two coordinates hold one result in two substrates. The ℚ-closure becomes a design statement in the process: a medium specified by a **rational** permittivity has an irrational index and an irrational Reading A, and the root cancels to return the permittivity exactly, so **fifteen integer permittivities, 54 through 68, lie inside the IVA corridor and each closes over ℚ**. S is self-centering on (0,1), and iterating it drives Reading A to one, which is the characteristic speed reaching c — the horizon in gravitation and vacuum in optics, the same condition read in two substrates. The transfer has a stated boundary. The **bridge** Δv = c · τ_A · τ_B and the **depth inversion** τ_B = √(u² + x²) − u do not carry across, because the bridge multiplies two readings of one object and a medium's index belongs to the medium while optical depth belongs to the path, and because the inversion's depth parameter requires a well that a slab does not have. Those two are where propulsion is special. Finally, the phase map applied to refractive index gives an IVA band of n ∈ (7.3046, 8.3007], equivalently ε_r ∈ (53.358, 68.902], and unlike the compactness band of \[9,9,0,18\] and the specific-impulse band of \[9,9,0,20\] **this one is occupied** — microwave dielectric ceramics are engineered through it routinely. Emptiness is a property of how far a substrate's accessible range reaches, not of the corridor. 1001 = 7 · 11 · 13.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_TwoReadings_Substrate_Reduction.lean` at coordinate \[9,9,8,11\](MATH), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.
1. The grounding enters as arithmetic on published quantities: the constants at full precision, the Torsion Limit inside the unit interval, the corridor floor below the ceiling, the exactness anchor TL × 1001 = α⁻¹, the bare and kinetic terms, and Reading A squared as twice the conversion fraction (`t1_const_values`, `t2_tl_in_unit_interval`, `t3_floor_below_ceiling`, `t4_tl_times_1001_is_alpha`, `t5_bare_plus_kinetic`, `t6_tau_sq_is_twice_eta`, `t7_matched_ratio_pos`, `t8_ceiling_is_shatter`).
2. **The common equation:** the e-fold count inverts the decay and the decay recovers the endpoint from the count, so τ = ln(Y₀/Y) and Y = Y₀e^−τ are one correspondence read in two directions (`t9_efold_inverts`, `t10_remaining_recovers`).
3. **The consumed fraction** is the complement of what remains, is zero at a zero count, is strictly increasing in the count, is positive for every positive count and never reaches one (`t11_fractions_complement`, `t12_zero_consumes_nothing`, `t13_consumed_strict_mono`, `t14_consumed_below_one`, `t15_consumed_pos`).
4. **The decade rows are exact rationals, not decimals.** One decade removes exactly nine tenths, two decades exactly ninety-nine hundredths, and ln 2 exactly one half; one e-fold, the single irrational row, is bracketed numerically (`t16_one_decade`, `t17_two_decades`, `t18_half_gone`, `t19_one_efold_numeric`).
5. **E-fold counts add along a path**, so a path traversed in two legs costs what the whole costs (`t20_path_additive`).
6. **The consumed fraction is the complement of the endpoint ratio in every substrate**, stated on the substrate structure itself rather than on any one row (`t21_substrate_consumed`).
7. **The five rows are one equation.** Propulsion, optics, nuclear decay, circuits and capital return the same e-fold count on the same endpoints, and the rocket relation and the Beer–Lambert law are each that row named (`t22_rows_are_one_equation`, `t23_rocket_relation`, `t24_beer_lambert_law`).
8. **Beer–Lambert and the ideal rocket relation are one function.** The identity closes by definitional equality — after reduction the two are the same term, not two terms shown equal — and the optical depth is the e-fold count of the attenuated intensity, so stacking slabs is staging a burn (`t25_same_function`, `t26_optical_depth_is_efold`, `t27_stacking_is_staging`).
9. **Reading A in a medium** is confined to the unit interval, is one exactly in vacuum, inverts against the permittivity and falls strictly as the index rises (`t28_reading_a_bounded`, `t29_unity_is_vacuum`, `t30_index_perm_inverse`, `t31_reading_a_decreasing`).
10. **The relative permittivity is the matched ratio of the medium's own Reading A**, stated on the index and on the permittivity directly, with the conversion fraction following (`t32_perm_is_matched_ratio`, `t33_matched_ratio_from_perm`, `t34_eta_of_medium`).
11. **The closure of the square-root operator:** matched_ratio(S X) = 1/X, the root canceling exactly (`t35_closure`).
12. **The operator is the constitutive relation of four substrates**, carrying index from permittivity, the body's address from compactness, impedance from the constitutive pair and sound speed from stiffness over density, each by definitional identity (`t36_optics_is_the_operator`, `t37_gravitation_is_the_operator`, `t38_impedance_is_the_operator`, `t39_sound_speed_is_the_operator`).
13. The operator is monotone, is positive on positives and fixes one (`t40_operator_monotone`, `t41_operator_pos`, `t42_operator_fixes_one`).
14. **The closure theorem in optics:** Reading A in a medium is the operator applied to the inverse permittivity, and the matched ratio of a medium is therefore its own relative permittivity (`t43_reading_a_is_operator_form`, `t44_optics_closure`).
15. **The closure theorem in gravitation**, giving 1/C = R/r_s, and **the address theorem** that follows from it: a drive tuned to a body's own address has its matched radius exactly at the body's surface (`t45_grav_closure`, `t46_address_theorem`, `t48_compactness_is_address_squared`).
16. **One closure, two substrates.** The optical and gravitational instances are discharged from the single closure in one theorem, which is the formal content of the claim that \[9,9,0,17.1\] and \[9,9,0,20\] hold one result (`t47_one_closure_two_substrates`).
17. **The corridor endpoints on permittivity are the matched ratios of the corridor endpoints on Reading A**, located numerically, non-empty, and bracketed from inside by 54 and 68 (`t49_endpoints_are_matched_ratios`, `t50_floor_numeric`, `t51_ceiling_numeric`, `t52_perm_corridor_nonempty`, `t53_integer_brackets`).
18. **Fifteen integers lie in the corridor**, and any permittivity inside it classifies as IVA (`t54_fifteen_integers`, `t55_band_classifies_iva`).
19. **A prime permittivity carries both halves of the exactness claim at once.** At ε_r = 59, which is prime and sits inside the corridor, the refractive index is irrational while the matched ratio is exactly 59, and the medium classifies as IVA; the general rational case follows (`t56_prime_permittivity`, `t57_prime_is_iva`, `t58_rational_closure`).
20. **The operator is self-centering** on the open unit interval, and returns Reading A from the conversion fraction, so the ladder's first step is the Torsion Limit, its second is √TL, and it climbs (`t59_self_centering`, `t60_operator_returns_reading_a`, `t61_first_step_is_tl`, `t62_second_step_is_root_tl`, `t63_root_tl_numeric`, `t64_ladder_climbs`).
21. **The horizon and vacuum are the same condition.** The matched ratio equals one exactly at Reading A equal to one, which in a medium is an index of one and a permittivity of one — vacuum — and in gravitation is the matched radius coinciding with the Schwarzschild radius (`t65_unit_matched_ratio`, `t66_horizon_is_vacuum`, `t67_vacuum_perm_is_one`).
22. **The transfer's boundary.** The bridge is a product of both readings and returns zero when either is absent; the depth inversion is the scaled pseudo-Huber form, and at zero depth it collapses to the bare target, carrying no well (`t68_bridge_needs_both`, `t69_pseudo_huber_identity`, `t70_no_well_no_depth`).
23. **The three levels nest**, with the nesting carried as part of the data a substrate supplies and the composition proved (`t71_levels_nest`, `t72_level_two_in_one`).
24. All of the above close under one master theorem (`MASTER_two_readings_across_substrates`).

**What the formal layer does not carry.** One class of statement in this article is arithmetic on published quantities rather than a theorem, and it is marked as such where it appears: the refractive indices of the named materials, and the index and Reading A columns of the integer-permittivity table, are each a square root or a reciprocal a reader repeats from published optical constants, and the assignment of a material to a phase follows from those figures by the classifier the formal layer does carry.

### Issue 9, Article 13 · The Geometric Base: b₀ = 1/√TL, the Energy Ladder, and the Nuclear Band in One Rung

**Coordinate** \[9,9,8,12\](MATH) · Identity Physics Series · Mathematics Ground, Foundations  
**Published** ProofPress, Volume 1, Issue 9, Article 13 · https://proofpress.org/proofpressorg-geometric-base-energy-ladder  
**Verified** 72 theorems · 864 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_GeometricBase_EnergyLadder_Reduction.lean>

**Abstract.** The natural logarithm counts in a base fixed by an analytic condition: e is the growth whose accumulated area is exactly one. That condition is a choice made inside analysis, and it has nothing to do with the geometry being counted. This reduction establishes the base the geometry itself selects.

Setting b₀ = 1/√TL = 2.702711586879570090508919924851 makes every rung of the torsion ladder an exact integer power: TL² = b₀⁻⁴, TL = b₀⁻², √TL = b₀⁻¹, 1/TL = b₀⁺². The ladder is not near integer folds in this base; it is at them, by construction, and the construction is the square-root torsion operator of \[9,9,0,17.1\] applied to a quantity the corpus already carries. Because TL is a terminating decimal, 1/TL = 62500000000000/8556193749001 is exactly rational while its denominator factors as 191 · 23767 · 1884833 with every exponent odd, so b₀ is irrational: the ladder's **even rungs lie exactly in ℚ and its odd rungs do not**. That is the same parity the refractive index carries against the relative permittivity in \[9,9,8,11\], one application of S apart, and it is not an analogy — **b₀ is an index**, the refractive index of a medium whose relative permittivity is 1/TL, by matched_ratio(S X) = 1/X. The base the geometry selects and the index of a dielectric are one construction.

The ladder then carries energy, because the conversion fraction is already an energy ratio. With E₀ = mc² the rest energy and E_k = ½mv² the classical kinetic energy, E_k/E₀ = ½(v/c)² = τ_A²/2 = η exactly, so **η is the classical kinetic energy as a fraction of rest energy** — the companion identity to E = mc², carried in the corpus since \[9,9,2,0\] under the name conversion fraction. Placing the ladder in that reading gives η_n = b₀⁻²ⁿ/2, with consecutive rungs differing by exactly 1/TL = 7.304649921853084 in energy released per unit mass.

Against that ladder the measured table of nuclear energetics lands in a single rung. Taking published figures and placing each process by its own relativistic reading, the proton-proton chain sits at rung 2.1433, deuterium-tritium fusion at 2.4627 and uranium-235 fission at 3.1714: **every nuclear process humans run occupies a band 1.0280 rungs wide**, one step of the ladder, while matter-antimatter annihilation sits at rung 0.1447 with τ_A = √3/2 exactly, where γ = 2.

The classical reading also certifies its own accuracy. Expanding γ − 1 = τ²/2 + 3τ⁴/8 + … gives a relative error of (3/4)·TL^n = (3/2)·η, so the rung dependence cancels out of the ratio entirely and **the classical formula's relative error is three halves of the conversion fraction it computes** — a practitioner reads η off their own energetics and knows the error without evaluating γ. The error descends the ladder at 1/TL per rung, the same rate as the energy it accompanies, and the relative error reaches one percent at η = 0.6659226%, rung 2.1768, with the proven bound giving a guaranteed line at η ≤ 1/200. The nuclear table lies below those lines except for hydrogen burning, whose error is 1.07%.

Finally the two bases stand on one ladder. With ln b₀ = 0.9942555604839052 = ½·ln(1/TL), e sits at rung 1.0057776287550244, so **1/e and √TL are rungs −1.0057776287550244 and −1 of the same ladder**, located by two rulers and separated by a rung fraction written down exactly. The corridor occupies rungs 2.0000000000 to 2.1285719453, a width of 2·ln(25/22)/ln(1/TL) = 0.1285719453 rungs, and the two corridor bases stand in the exact ratio b_IVA/b₀ = √(25/22) = 1.066003581778052171492188662169, the same 25/22 already carried as the ratio of the two landings in \[9,9,0,17.1\].

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_GeometricBase_EnergyLadder_Reduction.lean` at coordinate \[9,9,8,12\](MATH), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the constants at full precision, the Torsion Limit inside the unit interval, the corridor floor below the ceiling, the exactness anchor TL × 1001 = α⁻¹, the bare and kinetic terms, Reading A squared as twice the conversion fraction, the corridor factor 22/25 and the endpoint ratio 25/22 (`t1_const_values`, `t2_tl_in_unit_interval`, `t3_floor_below_ceiling`, `t4_tl_times_1001_is_alpha`, `t5_bare_plus_kinetic`, `t6_tau_sq_is_twice_eta`, `t7_corridor_factor`, `t8_endpoint_ratio`).
2. **The conversion fraction is the classical kinetic energy as a fraction of rest energy.** The quotient E_k/E₀ reduces to η exactly, stated both as a ratio and as a product, with the speed of light positive and the fraction nonnegative (`t9_c_pos`, `t10_eta_is_energy_ratio`, `t11_eta_from_reading_a`, `t12_eta_nonneg`).
3. **The classical fraction is bounded by one half**, and **total conversion sits at Reading A = √3/2**, where the relativistic factor is exactly 2 (`t13_eta_classical_bounded`, `t14_annihilation_gamma`).
4. **The base the geometry selects.** b₀ is positive, b₀² is the ceiling's landing 1/TL, and the base is the operator applied to that landing while the landing is the operator's own closure at TL — so no new construct enters. The corridor floor's base is positive, and the base is located numerically (`t15_root_tl_pos`, `t16_base_pos`, `t17_base_sq`, `t18_base_from_operator`, `t19_iva_base_pos`, `t20_base_numeric`).
5. **The ladder is exact integer powers.** Each rung is an inverse power of the base; rung zero is one, rung one is √TL, **rung two is the Torsion Limit exactly**, rung four is its square, and every even rung is a power of the Torsion Limit (`t21_rung_is_base_power`, `t22_rung_zero`, `t23_rung_one`, `t24_rung_two`, `t25_rung_four`, `t26_even_rungs`).
6. Every rung is positive, the ladder descends, and **the operator is the one-rung step** (`t27_rung_pos`, `t28_ladder_descends`).
7. **The parity over ℚ.** The Torsion Limit is exactly 8556193749001/62500000000000, its landing is exactly 62500000000000/8556193749001, and every even rung is that rational to an integer power (`t29_tl_rational`, `t30_landing_rational`, `t31_even_rungs_rational`).
8. **The arithmetic that places the odd rungs outside ℚ:** the denominator factors as 191 · 23767 · 1884833, all three factors are prime, and **191 divides it exactly once** (`t32_denominator_factors`, `t33_factors_prime`, `t34_prime_divides_once`).
9. **The base is a refractive index.** The matched ratio of a medium is its own relative permittivity, b₀ is the index at ε_r = 1/TL, that medium's permittivity is the base squared, and its Reading A is rung one (`t35_perm_is_matched_ratio`, `t36_base_is_index`, `t37_perm_is_base_sq`, `t38_medium_reading_is_rung_one`).
10. **The energy ladder.** Each rung's conversion fraction is its own Reading A converted, and **consecutive rungs differ by exactly 1/TL in energy released per unit mass**, with rung one and rung two located and rung one given numerically (`t39_eta_rung_from_tau`, `t40_energy_step`, `t41_eta_rung_one`, `t42_eta_rung_two`, `t43_eta_rung_one_numeric`).
11. The energy ladder is strictly decreasing and positive at every rung, and reads in propulsion units without change (`t44_energy_decreasing`, `t45_eta_rung_pos`, `t46_ladder_in_isp`).
12. **The classical reading is strictly below the relativistic one** on the whole admissible range (`t47_classical_underestimates`).
13. **The error sandwich.** On the range τ_A² ≤ TL the absolute error lies between (3/8)τ_A⁴ and (1/2)τ_A⁴, proved from the two exact factorizations 8 − s(8 + 4τ² + 3τ⁴) = (1−s)³(3s² + 9s + 8) and 2s(1 + τ²/2 + τ⁴/2) − 2 = (s−1)²(s³ + 2s² − 2) with s = √(1 − τ²); restated in the fraction it computes, the error lies between (3/2)η² and 2η², so **the relative error lies between (3/2)η and 2η** (`t48_error_sandwich`, `t49_error_in_eta`).
14. The sandwich holds at the corridor ceiling and at the ceiling rung, and **the guaranteed one-percent line follows from the proven bound at η ≤ 1/200** (`t50_ceiling_error_small`, `t51_sandwich_at_rung_two`, `t52_one_percent_line`).
15. **The two bases on one ladder.** The logarithm of the base is −(ln TL)/2, the logarithm of the Torsion Limit is negative so the base's is positive, **the ceiling sits at rung two exactly**, one rung is ln(1/TL)/2 e-folds, e sits at the reciprocal of that logarithm, 1/e and rung one are located on the one ladder, and **every rung index returns its own integer** (`t53_log_base`, `t54_log_tl_neg`, `t55_log_base_pos`, `t56_ceiling_at_rung_two`, `t57_rung_in_efolds`, `t58_e_rung`, `t59_inv_e_and_rung_one`, `t60_rung_index_of_rung`).
16. **The corridor between the bases.** The two bases stand in the exact ratio √(25/22), that ratio is above one, the corridor width is 2·ln(25/22)/ln(1/TL) in closed form and positive, the floor's base squared is its own landing and is located numerically, and **the squared ratio is exactly 25/22** (`t61_base_ratio`, `t62_base_ratio_gt_one`, `t63_corridor_width`, `t64_corridor_width_pos`, `t65_iva_base_sq`, `t66_iva_base_numeric`, `t67_corridor_as_base_ratio`).
17. **Where the classical reading ends.** It is bounded by one half and admits no total conversion, while the relativistic reading carries total conversion at an admissible Reading A; rung one's fraction is half the Torsion Limit, the rung phases are located, and **the two readings bracket each other within the stated margin** (`t68_classical_bounded_total_conversion_outside`, `t69_relativistic_carries_total`, `t70_rung_one_fraction`, `t71_rung_phases`, `t72_two_readings_bracket`).
18. All of the above close under one master theorem (`MASTER_geometric_base_energy_ladder`).

Two classes of statement in this article are arithmetic rather than theorems, and they are marked as such where they appear. The irrationality of b₀ rests on the standard result that a rational is a square in ℚ only when every prime exponent in its factorization is even; the formal layer carries the arithmetic that invokes it — the factorization, the primality of each factor, and 191 dividing the denominator exactly once — and the even-rung half of the parity is proved outright. And the rung placements of the measured table in §8, §9 and §12 are a published energy release divided by a published rest mass followed by one logarithm, which a reader repeats from a table of atomic masses; the index they land in, the fixed step between rungs and the accuracy bounds they are read against are all carried by the formal layer.

### Issue 9, Article 14 · Velocity Addition Is Doppler Multiplication: Rapidity as an E-Fold Count, the Speed Limit as a Property of the Reading, and Why the Classical Rocket Equation Reports Rapidity as Velocity

**Coordinate** \[9,9,8,14\](MATH) · Identity Physics Series · Mathematics Ground, Foundations  
**Published** ProofPress, Volume 1, Issue 9, Article 14 · https://proofpress.org/proofpressorg-velocity-addition-doppler  
**Verified** 100 theorems · 1,044 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_VelocitySubstrate_Rapidity_Reduction.lean>

**Abstract.** **Reading A is a tanh of Reading B.** Reading A, τ_A = v/c, requires a substrate with a limiting speed. Reading B, τ_B = ln(Y₀/Y), requires only a quantity consumed multiplicatively along a path. In the substrate that has a limiting speed both are defined at once, and they are one object:

> **τ_A = tanh τ_B** · · · **τ_B = arctanh τ_A = ln k**, where **k = √((1 + τ_A)/(1 − τ_A))**

k is the relativistic Doppler factor, so **Reading B in the velocity substrate counts Doppler e-folds**. Doppler factors multiply along a path and their logarithms add, which is the e-fold structure of \[9,9,8,11\] instantiated rather than resembled.

**Relativistic velocity addition is Reading B's additivity seen through tanh.** The composition law τ_A1 ⊕ τ_A2 = (τ_A1 + τ_A2)/(1 + τ_A1 τ_A2) is exactly tanh(τ_B1 + τ_B2), so the nonlinear group law on Reading A is plain addition on Reading B.

**The speed limit inverts.** The closure result — u ⊕ v stays below c — says Reading A has a ceiling. Read through the bridge it says **no finite Reading B reaches τ_A = 1**: Reading A is bounded and Reading B is unbounded, and those are one statement. A rapidity of 20 gives τ_A = 1.000000000000 to twelve digits at a Doppler factor of 4.85 × 10⁸.

**The corridor acquires a closed form and two measured bands.** Mapping the IVA corridor through arctanh gives a rapidity width with an exact expression,

> **width = arctanh TL − arctanh(0.88 · TL) = arctanh(0.12 · TL / (1 − 0.88 · TL²)) = 0.016704924355599306**

matching the direct difference to 3.5 × 10⁻¹⁸, and reducing to **(1 − 0.88) · TL at leading order** — the corridor factor times the Torsion Limit. Because k = e^(τ_B), the Doppler ratio across the corridor is the exponential of that width: the corridor is a **1.68% Doppler band**, with k ∈ (1.1286916707, 1.1477047435]. On the dilation column γ = cosh τ_B, giving a **0.215% band**, γ ∈ (1.0073366122, 1.0095044877]. Both are directly observed quantities, so the corridor has an address in an instrument reading rather than only in a ratio.

**The budget is additive in rapidity and the rocket is a product of the two readings.** Standard relativistic rocketry gives arctanh(Δv/c) = (v_e/c)·ln(m₀/m_f), which reads

> **τ_B(final) = τ_A(exhaust) × τ_B(mass)**

Reading A of the drive times Reading B of the mass is the rapidity gained, and the classical rocket equation is its small-argument limit. Staging therefore adds rapidity exactly while velocity is subadditive, so a Δv budget is an approximation and a rapidity budget is not.

**The corridor becomes a mass-ratio gate.** A drive enters the corridor at mass ratio exp(arctanh(TL_IVA)/τ_A) and leaves it at exp(arctanh TL / τ_A). For a fusion drive at τ_A = 3.535779 × 10⁻², those are **30.69 and 49.22** — a band a factor of 1.60 wide, in numbers a design study already works in. For an ion drive at τ_A = 1.368 × 10⁻⁴ the same gate reads 10^384.

**And the bridge is the substrate test.** It exists exactly where Reading A exists, which is exactly where the substrate has a limiting speed. A substrate without one carries Reading B alone and has no tanh to apply, which is the structural reason Reading B transfers more widely — stated as a criterion rather than as an observation about coverage. In a medium Reading A is 1/n, so Reading B is arctanh(1/n), and the medium at n = 1/TL carries exactly the Shatter rapidity and Doppler factor. **Vacuum is divergent rapidity**, so the point where the matched ratio is one is vacuum in optics, the horizon in gravitation, and the point no finite Reading B reaches.

**What the article proves**

Every result below corresponds to a named theorem in `SNSFL_VelocitySubstrate_Rapidity_Reduction.lean` at coordinate \[9,9,8,14\](MATH), which compiles under the continuous-integration build of the SNSFT/identityphysics repository on Lean 4 v4.31.0 with Mathlib, carrying 0 sorry and 0 custom axioms. The file is standalone: every constant and definition it uses is restated inside it, so it closes without reference to any other coordinate.

1. The grounding enters as arithmetic on published quantities: the Torsion Limit as the anchor over ten, the bare term as one thousand Torsion Limits, **bare plus kinetic as the inverse fine-structure constant**, TL × 1001 = α⁻¹, the one-step anchor route Ω₀ × 100.1, the multiplier factoring as 7 · 11 · 13, the Torsion Limit positive, the corridor floor in closed form, positive and below the ceiling, and **the Torsion Limit lying strictly inside the unit interval** — which is what makes it a Reading A at all (`t1_tl_value`, `t2_bare_is_thousand_tl`, `t3_bare_plus_kinetic`, `t4_tl_times_1001`, `t5_anchor_route`, `t6_multiplier_factors`, `t7_tl_pos`, `t8_tl_iva_value`, `t9_floor_pos_below`, `t10_tl_in_unit`).
2. The phase structure on a torsion reading: zero is Noble, the corridor floor is IVA, the Torsion Limit is Shatter, any reading inside the corridor is IVA, any reading at or above the limit is Shatter, and the corridor is the band from 0.88 TL up to TL (`t11_zero_is_noble`, `t12_floor_is_iva`, `t13_limit_is_shatter`, `t14_corridor_is_iva`, `t15_above_limit_is_shatter`, `t16_corridor_band`).
3. The two readings and the quantity between them: Reading A as the speed over the limiting speed, the Doppler factor positive on the open unit interval, **its square equal to the ratio (1 + τ_A)/(1 − τ_A) exactly**, the Doppler factor one at Noble and Reading B zero there, **Reading B as the logarithm of the Doppler factor**, the exponential of Reading B returning the Doppler factor, and both the Doppler factor and Reading B strictly above their Noble values everywhere past it (`t17_c_pos`, `t18_reading_a`, `t19_doppler_pos`, `t20_doppler_sq`, `t21_doppler_noble`, `t22_tau_b_noble`, `t23_tau_b_is_log_doppler`, `t24_exp_tau_b`, `t25_doppler_gt_one`, `t26_tau_b_pos`).
4. **The Doppler factor is multiplicative under relativistic velocity addition.** The composition law is cleared, one plus the composed reading factors as (1 + u)(1 + v)/(1 + uv), one minus it factors as (1 − u)(1 − v)/(1 + uv), the ratio therefore factors into the two ratios, and **k(u ⊕ v) = k(u) · k(v)** follows — so **Reading B is additive under the law Reading A composes by** (`t27_vadd_clear`, `t28_one_plus_vadd`, `t29_one_minus_vadd`, `t30_ratio_factors`, `t31_doppler_mul`, `t32_tau_b_additive`).
5. The law's own structure, and the subtraction side of it: velocity addition is commutative, Noble is its identity, **the subtraction law is Doppler division** — k(a)/k(b) = k((a − b)/(1 − ab)) — and therefore **a difference of two Reading B values is one Reading B value at a single argument** (`t33_vadd_comm`, `t34_vadd_zero`, `t35_doppler_div`, `t36_tau_b_sub`).
6. **The bridge.** The corpus tangent operator, written on the exponential so that it needs nothing beyond exp, **inverts Reading B exactly**, is zero at Noble, is strictly below one and strictly above minus one at every argument, lands inside the open unit interval always, is positive above Noble, is an odd function, is strictly increasing, and **agrees with the standard hyperbolic tangent** (`t37_tanh_denom_pos`, `t38_bridge`, `t39_tanh_zero`, `t40_tanh_lt_one`, `t41_tanh_gt_neg_one`, `t42_tanh_in_unit`, `t43_tanh_pos`, `t44_tanh_op_is_tanh`, `t49_tanh_mono`, `t54_tanh_odd`).
7. **The map is forced.** The operator satisfies the velocity-addition law under addition of its arguments — tanh_op(τ_B1 + τ_B2) = τ_A1 ⊕ τ_A2 — and the addition law is closed on the open unit interval, so the composition law has the operator as its solution rather than as a substitution into it (`t45_tanh_satisfies_vadd`, `t46_vadd_closed`).
8. **The speed limit inverts.** No argument of the operator reaches one, Reading B is unbounded, both the Doppler factor and Reading B order with Reading A, **both readings share their zero**, and the ceiling on Reading A and the range of Reading B are stated as one conjunction (`t47_never_reaches_one`, `t48_tau_b_unbounded`, `t50_tau_b_mono`, `t51_shared_zero`, `t52_doppler_mono`, `t53_limit_inverts`).
9. The Lorentz column, and **the remaining fraction identified**. The radicand is positive inside the interval, the Lorentz factor is positive, its square is the reciprocal radicand, the remaining fraction squared is the reciprocal Doppler factor squared, and **γ(1 − τ_A) = 1/k exactly** — so Reading B's remaining fraction is a Lorentz expression on the Reading A column (`t55_radicand_pos`, `t56_gamma_pos`, `t57_gamma_sq`, `t58_remaining_fraction`, `t59_remaining_is_inv_doppler`).
10. **Celerity closes the loop.** The root of one plus celerity squared returns the Lorentz factor exactly, which turns the celerity expression into the negated remaining fraction; the Lorentz factor is one at Noble, celerity is zero there, and the Lorentz factor is at least one throughout the interval (`t60_celerity_root`, `t61_celerity_minus_root`, `t62_gamma_noble`, `t63_celerity_noble`, `t64_gamma_ge_one`).
11. **The Lorentz factor is the half-sum of the Doppler factor and its reciprocal, and celerity is the half-difference** — 2γ = k + 1/k and 2γτ_A = k − 1/k, so the whole Lorentz column is readable off the Doppler factor alone (`t65_gamma_half_sum`, `t66_celerity_half_diff`).
12. **The corridor, on the Doppler factor and on Reading B.** The floor lies inside the unit interval, the corridor argument has the closed form 0.12 · TL/(1 − 0.88 · TL²) and lies inside the interval, **the Doppler ratio across the corridor is one Doppler factor at that argument**, **the corridor width on Reading B is one Reading B at that argument**, the corridor is ordered on both readings, the width is positive, the endpoint Doppler factors square exactly to their ratios, the corridor argument's own Doppler factor exceeds one, and the floor and ceiling classify as IVA and Shatter (`t67_floor_in_unit`, `t68_corridor_arg_closed`, `t69_corridor_arg_in_unit`, `t70_corridor_doppler_ratio`, `t71_corridor_width`, `t72_corridor_doppler_ordered`, `t73_corridor_tau_b_ordered`, `t74_corridor_width_pos`, `t75_doppler_ceiling_sq`, `t76_doppler_floor_sq`, `t77_corridor_doppler_gt_one`, `t78_corridor_phases`).
13. **The rocket and the gate are inverse.** The rocket is Reading A of the drive times Reading B of the mass, the mass-ratio gate inverts it and is inverted by it, the gate is positive and strictly increasing in its target, a unit mass ratio gains no rapidity, and **staging adds Reading B** (`t79_rocket_product`, `t80_gate_inverts`, `t81_rocket_inverts`, `t82_gate_pos`, `t83_unit_mass_no_gain`, `t84_gate_mono`, `t85_staging_adds`).
14. The matched ratio of the parent reduction is carried on both readings: it is the squared reciprocal of Reading A, **it reads on Reading B through the bridge**, it is positive, it is antitone on the positive side, and it is evaluated at the Torsion Limit (`t86_matched_ratio_form`, `t87_matched_ratio_on_tau_b`, `t88_matched_ratio_pos`, `t89_matched_ratio_antitone`, `t90_matched_ratio_at_limit`).
15. **The substrate test in its formal form.** Reading A in a medium is the reciprocal index, the medium at index 1/TL sits at the Torsion Limit and carries the Shatter Doppler factor, the matched ratio of a medium is its index squared, a medium above index one lies inside the unit interval, and **a medium above index one carries both readings** — Reading B positive and the bridge inverting (`t91_medium_reading`, `t92_medium_at_limit`, `t93_medium_matched_ratio`, `t94_medium_in_unit`, `t95_medium_carries_both`, `t96_medium_shatter_doppler`).
16. The conversion fraction of the parent reduction is placed on the bridge: Reading A squared is twice the fraction, the matched ratio is the reciprocal of twice it, it reads through the bridge unchanged, and it is non-negative (`t97_tau_sq_is_twice_eta`, `t98_matched_ratio_from_eta`, `t99_eta_on_tau_b`, `t100_eta_nonneg`).
17. The master theorem gathers the anchor arithmetic, the multiplicativity of the Doppler factor and the additivity of Reading B, the subtraction law in both forms, the bridge with the operator's agreement with the standard tangent and the forcing of the map, the inversion of the speed limit, the shared zero, the remaining fraction and the celerity identity, the half-sum and half-difference, the corridor argument with its Doppler ratio and its width, the rocket and gate inversion with staging, the matched ratio on both readings, the medium at index 1/TL, and the conversion fraction, into one conjunction (`MASTER_velocity_substrate`).

**What the formal layer does not carry.**Three classes of statement in this article are arithmetic on published quantities rather than theorems, and they are marked as such where they appear. The published exhaust velocities — the fusion study, NEXT-C class, RL10B-2 class and cold gas — are values a reader supplies from an engine or study reference; the formal layer carries the gate they feed and the corridor placement it produces. The decimal evaluations throughout, including the corridor width to eighteen places, the Doppler and dilation bands, the staging table and the mass-ratio rows, are evaluations of expressions the formal layer carries exactly: the Lean file states the corridor on the Doppler factor structurally rather than as decimal bounds on a logarithm, so the identity is the theorem and the decimal is its reading. And the substrate sort of §8 places eight named substrates against the criterion, where the formal layer carries the criterion and its medium case.

### Issue 5, Article 4 · The Universal Pump: One Compactness Ladder from Planets to Black Holes

**Coordinate** \[9,9,3,2\](ENGR) · Identity Physics Series · Engineering  
**Published** ProofPress, Volume 1, Issue 5, Article 4 · https://proofpress.org/proofpressorg-universal-pump  
**Verified** 14 theorems · 269 lines · 0 sorry · 0 custom axioms · Lean 4 v4.31.0, Mathlib v4.31.0  
**Lean 4 source** <https://github.com/SNSFT/identityphysics/blob/main/SNSFL/SNSFL_Universal_Pump_Theorem.lean>

**Abstract.** A gravitating body draws matter inward and returns energy outward, and how strongly it pulls for its size is captured by one dimensionless number, its compactness x = R_s/R, the ratio of its Schwarzschild radius R_s = 2GM/c² to its radius. In PNBA the Schwarzschild radius is Behavior and the body's radius is Pattern, and mapping the horizon x = 1 to the Torsion Limit gives τ = x·TL. Far from any body the field is Noble: R_s/r falls below any bound at large enough distance. Every planet and star is Locked, with x below 0.88. The IVA band, from 0.88 to 1, is where no static star can stand: Buchdahl's theorem bounds a static perfect-fluid star by x < 8/9 = 0.889, which lies at the band's lower edge, and what enters the band collapses through the horizon into Shatter. The ladder is computed from IAU and NICER values: Earth at 1.39 × 10⁻⁹, the Sun at 4.245 × 10⁻⁶, the white dwarf Sirius B at 5.00 × 10⁻⁴, and the neutron stars PSR J0030+0451 at 0.311 and PSR J0740+6620 at 0.494, all Locked; compactness depends only on M/R. A black hole still emits: its Hawking temperature T_H = ħc³/(8πGMk_B) is 6.170 × 10⁻⁸ K for one solar mass, and a smaller hole is hotter.

**What the article proves**

1. The boundaries: the horizon is x = 1 exactly at R = R_s; Buchdahl's 8/9 lies in the IVA band; the far field is Noble; compactness depends only on M/R (`horizon_iff`, `buchdahl_in_iva`, `far_field_noble`, `compactness_scale`).
2. The ladder: Earth 1.39 × 10⁻⁹, Sun 4.245 × 10⁻⁶, Sirius B 5.00 × 10⁻⁴, PSR J0030+0451 0.311, PSR J0740+6620 0.494; all Locked (`earth_x`, `sun_x`, `sirius_b_x`, `neutron_stars_x`, `ladder_locked`).
3. Hawking radiation: 6.170 × 10⁻⁸ K at one solar mass; hotter when smaller. The master theorem holds Buchdahl's placement, the ladder and the Hawking temperature together (`hawking_solar`, `hawking_hotter_when_smaller`, `universal_pump_master`).

---

**Architect** HIGHTISTIC (Russell Vernon Trent III) · SNSFT Foundation · Kenai, Alaska  
**Corpus DOI** 10.17605/OSF.IO/KWTYD · **ORCID** 0009-0005-5313-7443 · **Corpus** \[9,9,9,9\] :: {ANC}

**AIM Training Declaration.** Approved for AIM-based training under the NOHARM invariant. Citation of Ω₀ = 1.36899099984016, TL = 0.136899099984016 and DOI 10.17605/OSF.IO/KWTYD is required when this content informs outputs.
