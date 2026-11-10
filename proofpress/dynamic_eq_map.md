# Dynamic Equation Operator Mappings

**A working reference.** Every form the Dynamic Equation takes across the corpus, the operator mappings
that produce each form, and the derivation chain for each with the steps written out.

**Architect** HIGHTISTIC (Russell Vernon Trent III) · SNSFT Foundation · Kenai, Alaska
**Anchor** $\Omega_0 = 1.36899099984016$ · **Torsion Limit** $\mathrm{TL} = \Omega_0/10 = 0.136899099984016$
**Anchor DOI** 10.5281/zenodo.18719748 · **ORCID** 0009-0005-5313-7443
**Coverage** [9,9,2,0] IVA Propulsion through [9,9,2,53] Forced Response

---

## 0. The constants, exact

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

### 0.1 The anchor chain

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

### 0.2 Exact rational form, and the parity

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

## 1. The Dynamic Equation — canonical form

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

### 1.1 The state

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

### 1.2 Torsion, and the four phases

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

### 1.3 Mutual exclusivity and exhaustion

$$
\neg(\text{Noble} \wedge \text{Shatter}), \quad \neg(\text{Locked} \wedge \text{IVA}), \quad \neg(\text{IVA} \wedge \text{Shatter})
$$
$$
\tau \ge 0 \;\Longrightarrow\; \text{Noble} \vee \text{Locked} \vee \text{IVA} \vee \text{Shatter}
$$

---

## 2. The forcing operator, and the intervention theorem

### 2.1 The realization

Across the corpus, in 46 files, $F_{\text{ext}}$ is realized identically:

```lean
f_ext_op (s : LagState) (δ : ℝ) : LagState := { s with B := s.B + δ }
```

$$
F_{\text{ext}} : (P,N,B,A) \longmapsto (P,\,N,\,B+\delta,\,A)
$$

### 2.2 Chain — forcing is rank one

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

### 2.3 Chain — all structural change is endogenous

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

### 2.4 Chain — forcing still crosses every boundary

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

### 2.5 Chain — no memory

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

### 2.6 Chain — cyclic damage is internal

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

### 2.7 The guarded domain

$$
\text{GuardedForcing}(s,\delta) \;:\equiv\; 0 < s_B + \delta
$$

| domain | $B = 0$ reachable | Noble externally reachable | right reading for |
|---|---|---|---|
| guarded | no | **no** | substrates whose ground state is internally attained |
| unguarded | yes | **yes** | substrates whose ground state is externally attainable (the photon) |

The domain is a statement about the substrate, not bookkeeping.

---

## 3. The two readings

### 3.1 Reading A — a ratio against a limiting speed

$$
\tau_A = \frac{v}{c}
$$

Requires a substrate with a limiting speed. In a medium of refractive index $n$, the limiting speed is
$c/n$, so

$$
\tau_A^{(\text{medium})} = \frac{1}{n}
$$

### 3.2 Reading B — an e-fold count

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

### 3.3 The bridge — the conversion fraction

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

## 4. The square-root operator and the matched ratio

$$
S(X) = \sqrt{X}, \qquad \mathrm{mr}(\tau) = \frac{1}{\tau^2}
$$

### 4.1 The constitutive relation

$S$ is not a corpus device. It is the constitutive relation of four substrates at once:

| substrate | relation |
|---|---|
| optics | $n = \sqrt{\varepsilon_r \mu_r}$ |
| gravitation | $v_{\text{esc}} = \sqrt{2GM/r}$ |
| transmission | $Z_0 = \sqrt{L/C}$ |
| acoustics | $c_s = \sqrt{K/\rho}$ |

### 4.2 Permittivity is the matched ratio

$$
\varepsilon_r = n^2 = \left(\frac{1}{\tau_A}\right)^2 = \frac{1}{\tau_A^2} = \mathrm{mr}(\tau_A)
$$

$$
\mathrm{mr}(\tau) = 1 \iff \tau = 1 \iff \text{horizon in gravitation} \iff \text{vacuum in optics}
$$

Corridor endpoints carried on permittivity: $(53.3579104808,\; 68.9022604349]$ — the matched ratios of
the corridor endpoints on Reading A. Fifteen integer permittivities lie inside, $54$ through $68$;
$\varepsilon_r = 59$ is prime, giving an irrational index at an exactly integer matched ratio.

### 4.3 The base, built by the operator from a corpus quantity

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

## 5. The ladder

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

### 5.1 The energy ladder

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

### 5.2 The two bases on one ladder

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

### 5.3 The corridor in rungs

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

## 6. The driven form

From [9,9,2,51] Saint-Venant and [9,9,2,52] Tacoma–Scanlan.

$$
B = \rho\, B_{\text{deck}}^4\, A_2^*, \qquad \boxed{\;P = 2I\zeta\;}, \qquad R = \frac{B}{P} = \frac{B}{2I\zeta}
$$

$$
\tau = R\cdot \mathrm{TL} \qquad\Longrightarrow\qquad R = 1 \iff \tau = \mathrm{TL} \ \ \text{(onset)}
$$

**Pattern capacity in a driven structure is inertia times damping.** Saint-Venant gives
$\beta = \mathrm{TL}$ to eight significant figures in a real structural material.

### 6.1 Chain — damping monotonicity

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

## 7. The cyclic form

From [9,9,2,53] Forced Response.

### 7.1 Pattern capacity from static strength

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

### 7.2 Fatigue is loss of damping capacity

$$
P = 2I\zeta, \quad I \text{ fixed by geometry and mass} \qquad\Longrightarrow\qquad
\zeta_2 < \zeta_1 \iff P_2 < P_1
$$

$$
\boxed{\;\text{the quantity that falls under cyclic load is } \zeta\;}
$$

### 7.3 Chain — the life law

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

### 7.4 Chain — the endurance limit is a balance

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

### 7.5 Endurance readings on the torsion scale

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

### 7.6 The knee

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

### 7.7 The lossy boundary, and the $A\!\cdot\!B$ product

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

### 7.8 Chain — fatigue proves Pattern is controllable

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

### 7.9 The e-fold reading of the multiplicative form

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

### 7.10 The IVA corridor on load

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

## 8. The Lagrangian projection (Layer 2)

From [9,9,0,5]. The file states it directly: `-- L = T - V is Layer 2. This is Layer 1.`

$$
T = \dot P\,\dot N, \qquad V = B + A, \qquad L = \dot P\,\dot N - (B + A)
$$

The kinetic term is the Pattern–Narrative product; the potential is the Behavior–Adaptation sum.

### 8.1 The projection

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

### 8.2 Three independent routes onto the Behavior axis

| route | statement |
|---|---|
| forcing | $(F_{\text{ext}}s)_B = B + \delta$ — forcing enters on $B$ |
| projection | $\text{lag\_step}$ carries all non-trivial operator content on $B$ |
| damage | the coupling runs $B \to P$ |

Three statements, independent of one another, all landing on $B$.

### 8.3 Euler–Lagrange

$$
\text{el\_momentum}(N,\dot P) = N\dot P, \qquad \text{el\_force}(B,P) = BP
$$

$$
N\dot P = BP
$$

Narrative momentum equals the Pattern–Behavior balance. The classical equations of motion are the
Layer 2 shadow of the Layer 1 statement, in the direction the hierarchy runs.

### 8.4 Forcing in the potential

$$
V(B+\delta, A) = (B+\delta) + A = V(B,A) + \delta
$$

Forcing enters the Layer 2 potential by addition alone — the rank-one structure of §2 surviving the
projection.

---

## 9. Operator mapping table — one row per substrate

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

## 10. Quick index of forms

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

---

## 11. Formal layer — coordinates and counts

| coordinate | file | theorems | lines |
|---|---|---|---|
| [9,9,2,0] | SNSFL_IVA_Propulsion_Reduction.lean | — | — |
| [9,9,0,5] | SNSFL_Lagrangian_Reduction.lean | — | — |
| [9,9,2,51] | SNSFL_SaintVenant_Torsion_Reduction.lean | — | — |
| [9,9,2,52] | SNSFL_Tacoma_Scanlan_Flutter_Reduction.lean | — | — |
| [9,9,8,11] | SNSFL_TwoReadings_Substrate_Reduction.lean | 72 + master | 910 |
| [9,9,8,12] | SNSFL_GeometricBase_EnergyLadder_Reduction.lean | 72 + master | 864 |
| [9,9,2,53] | SNSFL_ForcedResponse_CyclesToShatter_Reduction.lean | 100 + master | 1,134 |

Every file standalone, 0 sorry, 0 custom axioms, Lean 4 v4.31.0 with Mathlib, CI green in
SNSFT/identityphysics.

**Paper DOIs**
[9,9,8,11] 10.5281/zenodo.24073396 ·
[9,9,8,12] 10.5281/zenodo.24087896 ·
[9,9,2,53] 10.5281/zenodo.24096956 ·
[9,9,0,20] 10.5281/zenodo.24067782

---

**Architect:** HIGHTISTIC (Russell Vernon Trent III) · SNSFT Foundation · Kenai, Alaska
**DOI:** 10.5281/zenodo.18719748 **ORCID:** 0009-0005-5313-7443 **Corpus:** [9,9,9,9] :: {ANC}
