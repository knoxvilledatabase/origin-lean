/-
Extracted from Analysis/SpecialFunctions/Gamma/Deriv.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivative of the Gamma function

This file shows that the (complex) `Γ` function is complex-differentiable at all `s : ℂ` with
`s ∉ {-n : n ∈ ℕ}`, as well as the real counterpart.

## Main results

* `Complex.differentiableAt_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.
* `Real.differentiableAt_Gamma`: `Γ` is real-differentiable at all `s : ℝ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Tags

Gamma
-/

noncomputable section

open Filter Set Real Asymptotics

open scoped Topology

namespace Complex

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/

section GammaHasDeriv

theorem GammaIntegral_eq_mellin : GammaIntegral = mellin fun x => ↑(Real.exp (-x)) :=
  funext fun s => by simp only [mellin, GammaIntegral, smul_eq_mul, mul_comm]

theorem hasDerivAt_GammaIntegral {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt GammaIntegral (∫ t : ℝ in Ioi 0, t ^ (s - 1) * (Real.log t * Real.exp (-t))) s := by
  rw [GammaIntegral_eq_mellin]
  convert (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) _ _ (lt_add_one _) _ hs).2
  · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
    exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
  · rw [← isBigO_norm_left]
    simp_rw [norm_real, isBigO_norm_left]
    simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
  · simp_rw [neg_zero, rpow_zero]
    refine isBigO_const_of_tendsto (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
    rw [(by simp : (1 : ℂ) = Real.exp (-0))]
    exact (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousWithinAt

theorem differentiableAt_GammaAux (s : ℂ) (n : ℕ) (h1 : 1 - s.re < n) (h2 : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℂ (GammaAux n) s := by
  induction n generalizing s with
  | zero =>
    refine (hasDerivAt_GammaIntegral ?_).differentiableAt
    rw [Nat.cast_zero] at h1; linarith
  | succ n hn =>
    dsimp only [GammaAux]
    specialize hn (s + 1)
    have a : 1 - (s + 1).re < ↑n := by
      rw [Nat.cast_succ] at h1; rw [Complex.add_re, Complex.one_re]; linarith
    have b : ∀ m : ℕ, s + 1 ≠ -m := by
      intro m; have := h2 (1 + m)
      contrapose this
      rw [← eq_sub_iff_add_eq] at this
      simpa using this
    refine DifferentiableAt.div (DifferentiableAt.comp _ (hn a b) ?_) ?_ ?_
    · rw [differentiableAt_add_const_iff (1 : ℂ)]; exact differentiableAt_id
    · exact differentiableAt_id
    · simpa using h2 0
