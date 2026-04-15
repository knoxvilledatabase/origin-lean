/-
Extracted from NumberTheory/LSeries/HurwitzZetaValues.lean
Genuine: 4 of 14 | Dissolved: 10 | Infrastructure: 0
-/
import Origin.Core

/-!
# Special values of Hurwitz and Riemann zeta functions

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers. More generally, we give formulae for any Hurwitz zeta functions at any (strictly) negative
integer in terms of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib/NumberTheory/ZetaValues.lean`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.
- `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## TODO

* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

open Complex Real Set

open scoped Nat

namespace HurwitzZeta

variable {k : ℕ} {x : ℝ}

-- DISSOLVED: cosZeta_two_mul_nat

-- DISSOLVED: sinZeta_two_mul_nat_add_one

-- DISSOLVED: cosZeta_two_mul_nat'

-- DISSOLVED: sinZeta_two_mul_nat_add_one'

-- DISSOLVED: hurwitzZetaEven_one_sub_two_mul_nat

-- DISSOLVED: hurwitzZetaOdd_neg_two_mul_nat

-- DISSOLVED: hurwitzZeta_one_sub_two_mul_nat

-- DISSOLVED: hurwitzZeta_neg_two_mul_nat

-- DISSOLVED: hurwitzZeta_neg_nat

end HurwitzZeta

open HurwitzZeta

-- DISSOLVED: riemannZeta_two_mul_nat

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

theorem riemannZeta_neg_nat_eq_bernoulli' (k : ℕ) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli', bernoulli, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, ← neg_one_mul, ← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow, neg_one_mul (-1),
    neg_neg, one_pow, one_mul]
