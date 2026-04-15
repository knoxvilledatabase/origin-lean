/-
Extracted from NumberTheory/LSeries/HurwitzZetaOdd.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaOdd a s = 1 / 2 * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`sinZeta a s = ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`.

The term for `n = -a` in the first sum is understood as 0 if `a` is an integer, as is the term for
`n = 0` in the second sum (for all `a`). Note that these functions are differentiable everywhere,
unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed sine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* `hasSum_int_hurwitzZetaOdd` and `hasSum_nat_sinZeta`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

noncomputable section

open Complex

open CharZero Filter Topology Asymptotics Real Set MeasureTheory

open scoped ComplexConjugate

namespace HurwitzZeta

section kernel_defs

/-!
## Definitions and elementary properties of kernels
-/

def jacobiTheta₂'' (z τ : ℂ) : ℂ :=
  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)

lemma jacobiTheta₂''_conj (z τ : ℂ) :
    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg,
    neg_div, jacobiTheta₂'_neg_left]

lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc]
  refine congr_arg (· / (2 * π * I)) ?_
  -- get all exponential terms to left
  rw [mul_left_comm _ (cexp _), ← mul_add, mul_assoc (cexp _), ← mul_add, ← mul_assoc (cexp _),
    ← Complex.exp_add]
  congrm (cexp ?_ * ?_) <;> ring

lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div, -neg_add_rev, ← neg_add]

lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) :
    jacobiTheta₂' z τ = (-2 * π) / (-I * τ) ^ (3 / 2 : ℂ) * jacobiTheta₂'' z (-1 / τ) := by
  rcases eq_or_ne τ 0 with rfl | hτ
  · rw [jacobiTheta₂'_undef _ (by simp), mul_zero, zero_cpow (by simp), div_zero, zero_mul]
  have aux1 : (-2 * π : ℂ) / (2 * π * I) = I := by
    rw [div_eq_iff two_pi_I_ne_zero, mul_comm I, mul_assoc _ I I, I_mul_I, neg_mul, mul_neg,
      mul_one]
  rw [jacobiTheta₂'_functional_equation, ← mul_one_div _ τ, mul_right_comm _ (cexp _),
    (by rw [cpow_one, ← div_div, div_self (neg_ne_zero.mpr I_ne_zero)] :
      1 / τ = -I / (-I * τ) ^ (1 : ℂ)), div_mul_div_comm,
    ← cpow_add _ _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ), ← div_mul_eq_mul_div,
    (by norm_num : (1 / 2 + 1 : ℂ) = 3 / 2), mul_assoc (1 / _), mul_assoc (1 / _),
    ← mul_one_div (-2 * π : ℂ), mul_comm _ (1 / _), mul_assoc (1 / _)]
  congr 1
  rw [jacobiTheta₂'', div_add' _ _ _ two_pi_I_ne_zero, ← mul_div_assoc, ← mul_div_assoc,
    ← div_mul_eq_mul_div (-2 * π : ℂ), mul_assoc, aux1, mul_div z (-1), mul_neg_one, neg_div τ z,
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left, neg_mul, ← mul_neg, ← mul_neg,
    mul_div, mul_neg_one, neg_div, neg_mul, neg_mul, neg_div]
  congr 2
  rw [neg_sub, ← sub_eq_neg_add, mul_comm _ (_ * I), ← mul_assoc]
