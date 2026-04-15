/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`.

## Main statements

* integrable_measureT: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* integral_eval_T_real_mul_evalT_real_measureT_of_ne:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* integral_eval_T_real_mul_self_measureT_zero:
  if `n = m = 0` then the integral equals `π`.
* integral_eval_T_real_mul_self_measureT_of_ne_zero:
  if `n = m ≠ 0` then the integral equals `π / 2`.

## TODO

* Prove that Chebyshev U polynomials are orthogonal with respect to `√(1 - x ^ 2)`
* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT

-/

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal

noncomputable def measureT : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num), measureT,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x ↦ √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx ↦ ?_) (by simp)
  simpa using (hasDerivAt_arccos (by aesop) (by aesop)).neg

theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at this
  rw [measureT, restrict_withDensity (by measurability),
    integrable_withDensity_iff (by fun_prop) (by simp)]
  unfold IntegrableOn at this
  convert this

open Set in
