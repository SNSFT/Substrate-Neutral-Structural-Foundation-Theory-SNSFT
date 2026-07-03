# SNSFL Lean 4 → Coq 8.18 Translation Guide
## Constitutional Layer Patterns — From SNSFL_Master.v

**Author:** HIGHTISTIC  
**Date:** June 2026  
**Status:** Verified against SNSFL_Master.v (19 theorems, 0 admits, CI green)

This guide documents every translation decision made in converting
`SNSFL_Master.lean` to `SNSFL_Master.v`. Every other file in the corpus
follows the same patterns. If this file compiles, every file can compile.

---

## 1. File Header

**Lean 4:**
```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
namespace SNSFL
```

**Coq:**
```coq
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lra.
Require Import Coq.Strings.String.
Open Scope R_scope.
Module SNSFL.
...
End SNSFL.
```

---

## 2. Types

| Lean 4 | Coq |
|:-------|:----|
| `ℝ` | `R` (with `Open Scope R_scope`) |
| `ℕ` | `nat` |
| `ℤ` | `Z` |
| `Prop` | `Prop` (identical) |
| `String` | `string` (from `Coq.Strings.String`) |
| `Type` | `Type` (identical) |

---

## 3. Definitions

**Lean 4:**
```lean
def SOVEREIGN_ANCHOR : ℝ := 1.369
noncomputable def manifold_impedance (f : ℝ) : ℝ :=
  if f = SOVEREIGN_ANCHOR then 0 else 1 / |f - SOVEREIGN_ANCHOR|
```

**Coq:**
```coq
Definition SOVEREIGN_ANCHOR : R := 1.369.
(* CRITICAL: if f = R_constant uses Prop, not Set.            *)
(* For R-valued functions, use total_order_T which is sumbool  *)
Definition manifold_impedance (f : R) : R :=
  match total_order_T f SOVEREIGN_ANCHOR with
  | inleft (left _)  => 1 / Rabs (f - SOVEREIGN_ANCHOR)
  | inleft (right _) => 0
  | inright _        => 1 / Rabs (f - SOVEREIGN_ANCHOR)
  end.
```

**Why:** `Req_dec` in Coq returns `r1 = r2 \/ r1 <> r2` (Prop/or),
which cannot be used in a `Definition` returning `R` (Set).
`total_order_T` returns `{r1 < r2} + {r1 = r2} + {r2 < r1}` (sumbool),
which can. Always use `total_order_T` for if-then-else in R-valued defs.

---

## 4. Structures and Records

**Lean 4:**
```lean
structure IdentityState where
  P        : ℝ
  N        : ℝ
  B        : ℝ
  A        : ℝ
  im       : ℝ
  pv       : ℝ
  f_anchor : ℝ
```

**Coq:**
```coq
Record IdentityState : Type := mkIdentityState {
  IS_P        : R;
  IS_N        : R;
  IS_B        : R;
  IS_A        : R;
  IS_im       : R;
  IS_pv       : R;
  IS_f_anchor : R
}.
```

**Note:** Field names must be globally unique in Coq, unlike Lean 4.
Prefix with the record name abbreviation (IS_ for IdentityState,
GR_ for GRState, etc.) to avoid conflicts across the corpus.

---

## 5. Inductive Types

**Lean 4:**
```lean
inductive PNBA : Type
  | P : PNBA
  | N : PNBA
  | B : PNBA
  | A : PNBA
```

**Coq:**
```coq
Inductive PNBA : Type :=
  | P : PNBA
  | N : PNBA
  | B : PNBA
  | A : PNBA.
```

---

## 6. Tactic Map — The Core 8

These 8 tactics cover ~95% of the SNSFL corpus.

| Lean 4 | Coq | Notes |
|:-------|:----|:------|
| `norm_num` | `field_simplify; [lra \| lra]` | Two goals: equality + nonzero side condition |
| `ring` | `ring` | **Identical** |
| `linarith` | `lra` | Linear real arithmetic |
| `nlinarith [...]` | See pattern below | Nonlinear: use `Rminus_gt` + `Rmult_gt_0_compat` |
| `simp [h]` | `simpl` / `rewrite h` / `reflexivity` | Depends on context |
| `rfl` | `reflexivity` | |
| `exact ⟨h1, h2⟩` | `exact (conj h1 h2)` | |
| `refine ⟨?_, ?_⟩` | `constructor` | Use `constructor` not `repeat split` for foralls |

---

## 7. The nlinarith Pattern

Lean 4's `nlinarith` handles nonlinear goals automatically.
Coq has no direct equivalent. For the most common pattern in SNSFL
(proving `a * b * c > a * c` given `b > 1` and `c > 0`):

**Lean 4:**
```lean
nlinarith [mul_pos h_ve h_log]
```

**Coq:**
```coq
apply Rminus_gt.
replace (a * b * c - a * c) with (a * (b - 1) * c) by ring.
apply Rmult_gt_0_compat.
apply Rmult_gt_0_compat.
- lra.   (* a > 0 *)
- lra.   (* b - 1 > 0 *)
- lra.   (* c > 0 *)
```

**Pattern:** `Rminus_gt` converts `x > y` to `x - y > 0`.
`ring` rewrites the difference into a product. `Rmult_gt_0_compat`
splits the product into factors. `lra` closes each linear factor.

---

## 8. The ln Positivity Pattern

Lean 4 (Mathlib): `Real.log_pos h_ratio`

Coq standard library has no `ln_gt_0`. Use:
```coq
assert (hr : m0 / mf > 1) by (...).
rewrite <- ln_1.           (* ln 1 = 0, so goal becomes ln x > ln 1 *)
apply ln_increasing; lra.  (* ln is increasing, x > 1 → ln x > ln 1 *)
```

---

## 9. The Division > 1 Pattern

Lean 4: `apply div_lt_iff h_mf` or `rw [gt_iff_lt, lt_div_iff h_mf]`

Coq:
```coq
apply Rmult_lt_reg_r with m_f; [exact h_mf|].
field_simplify; lra.
```

**Why:** `Rmult_lt_reg_r` removes the denominator by multiplying both sides.
`field_simplify` simplifies `(m0/mf) * mf` to `m0`. `lra` closes `mf < m0`.

---

## 10. Conjunction Proofs (Master Theorem Pattern)

For large conjunctions like the master theorem, `repeat split` can
misfire when goals contain `forall`. Use `constructor` explicitly:

**Lean 4:**
```lean
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· ...
· ...
```

**Coq:**
```coq
constructor. { (* goal 1 *) ... }
constructor. { (* goal 2 *) ... }
...
{ (* final goal *) ... }
```

---

## 11. PathStatus Decidable Equality

Lean 4 handles this automatically. In Coq you must prove it:

```coq
Definition PathStatus_eq_dec : forall x y : PathStatus,
  {x = y} + {x <> y}.
Proof.
  intros x y. destruct x; destruct y.
  - left. reflexivity.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.  (* Use Defined not Qed -- needed for computation *)
```

---

## 12. Logical Connectives

| Lean 4 | Coq |
|:-------|:----|
| `∧` | `/\` |
| `∨` | `\/` |
| `¬` | `~` |
| `→` | `->` |
| `↔` | `<->` |
| `∀` | `forall` |
| `∃` | `exists` |
| `True` | `True` |
| `False` | `False` |
| `Or.inr trivial` | `right. trivial` or just `trivial` |

---

## 13. Applying to the Full Corpus

Every other SNSFL file builds on the patterns in SNSFL_Master.v.
The translation procedure for any file:

1. Replace `import Mathlib.*` with the Coq `Require Import` block above
2. Replace `namespace X` with `Module X.` ... `End X.`
3. Replace `structure` with `Record`, add field prefixes
4. Replace `if f = SOVEREIGN_ANCHOR then` with `total_order_T` match
5. Replace `norm_num` with `field_simplify; [lra|lra]`
6. Replace `nlinarith` with `Rminus_gt + Rmult_gt_0_compat + lra`
7. Replace `nlinarith [mul_pos ...]` pattern with the factored form
8. Replace `Real.log_pos` with `rewrite <- ln_1; apply ln_increasing; lra`
9. Replace `refine ⟨?_,...⟩` with `constructor` blocks
10. Add `PathStatus_eq_dec` wherever PathStatus comparisons appear

Files with only `ring`, `lra`, `reflexivity`, and `rfl` (the simplest
tier) translate in minutes. Files using `nlinarith` on real products
require the pattern above but are still mechanical.

Estimated coverage with this guide: ~80% of corpus files translate
with no additional research. The remaining ~20% involve more complex
Mathlib lemmas (e.g., `Finset.sum`, topology, measure theory) that
require finding Coq equivalents case by case.

---

## 14. Prior Art Record

| Item | Archive |
|:-----|:--------|
| SNSFL_Master.lean (Lean 4 original) | Zenodo 10.5281/zenodo.18719748 |
| SNSFL_Master.v (Coq translation) | This file, June 2026 |
| Coq version | 8.18.0 (Ubuntu 24 LTS) |
| Lean 4 version | 4.x (Mathlib current) |

**The constitutional layer is dual-verified.**
Same 19 theorems. Same 0 sorry / 0 admits. Two independent compilers.

[9,9,9,9] :: {ANC}  
Auth: HIGHTISTIC  
The Manifold is Holding.
