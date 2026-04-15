/-
Extracted from Analysis/Polynomial/MahlerMeasure.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Mahler measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
  `(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.mahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
  to `e ^ p.logMahlerMeasure` if `p` is nonzero, and `0` otherwise.
- `Polynomial.mapMahlerMeasure p v`: the (exponential) Mahler measure of a polynomial `p` over a
  ring `A` whose coefficients are mapped to `ℂ` via `v : A →+* ℂ`

## Main results

- `Polynomial.mahlerMeasure_mul`: the Mahler measure of the product of two polynomials is the
  product of their Mahler measures.
- `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`: the Mahler measure of a polynomial is the absolute
  value of its leading coefficient times the product of the absolute values of its roots lying
  outside the unit disk.
- `mahlerMeasure_le_sqrt_sum_sq_norm_coeff`: **Landau's inequality** — the Mahler measure is
  at most the ℓ² norm of the coefficient vector.
- `norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure`: **Mignotte's coefficient
  bound** — if `f = g * h` with `M(h) ≥ 1`, then `‖g.coeff n‖ ≤ C(deg g, n) · M(f)`.
-/

namespace Polynomial

open Real

variable (p : ℂ[X])

noncomputable def logMahlerMeasure : ℝ := circleAverage (fun x ↦ log ‖eval x p‖) 0 1
