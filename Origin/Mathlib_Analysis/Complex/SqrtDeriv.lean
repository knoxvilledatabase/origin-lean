/-
Extracted from Analysis/Complex/SqrtDeriv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of `Complex.sqrt`

This file proves that `Complex.sqrt` is differentiable on the slit plane
`Complex.slitPlane` and computes its derivative.

## Main results

* `Complex.hasDerivAt_sqrt`: the derivative of `Complex.sqrt` at `z ∈ slitPlane`
  is `z ^ (-1 / 2 : ℂ) / 2`.
* `Complex.differentiableOn_sqrt`: `Complex.sqrt` is differentiable on `slitPlane`.
* `Complex.deriv_sqrt`: the derivative equals `z ^ (-1 / 2 : ℂ) / 2`.
-/

namespace Complex

lemma hasStrictDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) :
    HasStrictDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z := by
  exact (Complex.hasStrictDerivAt_cpow_const (c := 2⁻¹) hz).congr_deriv (by
    rw [show (2 : ℂ)⁻¹ - 1 = -1 / 2 by norm_num, mul_comm, ← div_eq_mul_inv])

lemma hasDerivAt_sqrt {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt sqrt (z ^ (-1 / 2 : ℂ) / 2) z :=
  (hasStrictDerivAt_sqrt hz).hasDerivAt

lemma hasDerivWithinAt_sqrt {z : ℂ} {s : Set ℂ} (hz : z ∈ slitPlane) :
    HasDerivWithinAt sqrt (z ^ (-1 / 2 : ℂ) / 2) s z :=
  (hasDerivAt_sqrt hz).hasDerivWithinAt
