/-
Extracted from NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean
Genuine: 5 of 8 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Analytic part of the Lindemann-Weierstrass theorem
-/

namespace LindemannWeierstrass

noncomputable section

open scoped Nat

open Complex Polynomial

set_option backward.isDefEq.respectTransparency false in

theorem hasDerivAt_cexp_mul_sumIDeriv (p : ℂ[X]) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -(cexp (-(x • s)) * p.sumIDeriv.eval (x • s)))
      (s * (cexp (-(x • s)) * p.eval (x • s))) x := by
  have h₀ := (hasDerivAt_id' x).smul_const s
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((sumIDeriv p).hasDerivAt (x • s)).comp x h₀
  convert (h₁.mul h₂).fun_neg using 1
  nth_rw 1 [sumIDeriv_eq_self_add p]
  simp only [one_smul, eval_add, Function.comp_apply]
  ring

set_option backward.isDefEq.respectTransparency false in

theorem integral_exp_mul_eval (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in 0..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIDeriv.eval s) + p.sumIDeriv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_cexp_mul_sumIDeriv p s x)
      (ContinuousOn.intervalIntegrable (by fun_prop))]
  simp

private def P (f : ℂ[X]) (s : ℂ) :=
  exp s * f.sumIDeriv.eval 0 - f.sumIDeriv.eval s

private theorem P_eq_integral_exp_mul_eval (f : ℂ[X]) (s : ℂ) :
    P f s = exp s * (s * ∫ x in 0..1, exp (-(x • s)) * f.eval (x • s)) := by
  rw [integral_exp_mul_eval, mul_add, mul_neg, exp_neg, mul_inv_cancel_left₀ (exp_ne_zero s),
    neg_add_eq_sub, P]

set_option backward.isDefEq.respectTransparency false in

private theorem P_le_aux (f : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(f p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p : ℕ,
      ‖P (f p) s‖ ≤
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [P_eq_integral_exp_mul_eval (f p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

-- DISSOLVED: P_le

-- DISSOLVED: exp_polynomial_approx_aux

-- DISSOLVED: exp_polynomial_approx

end

end LindemannWeierstrass
