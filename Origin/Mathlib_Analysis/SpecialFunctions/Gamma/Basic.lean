/-
Extracted from Analysis/SpecialFunctions/Gamma/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Gamma function

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `Complex.Gamma`: the `Γ` function (of a complex variable).
* `Complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `Complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `Complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.

## Gamma function: main statements (real case)

* `Real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`.

## Tags

Gamma
-/

noncomputable section

open Filter intervalIntegral Set Real MeasureTheory Asymptotics

open scoped Nat Topology ComplexConjugate

namespace Real

theorem Gamma_integrand_isLittleO (s : ℝ) :
    (fun x : ℝ => exp (-x) * x ^ s) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  refine isLittleO_of_tendsto (fun x hx => ?_) ?_
  · exfalso; exact (exp_pos (-(1 / 2) * x)).ne' hx
  have : (fun x : ℝ => exp (-x) * x ^ s / exp (-(1 / 2) * x)) =
      (fun x : ℝ => exp (1 / 2 * x) / x ^ s)⁻¹ := by
    ext1 x
    simp [field, ← exp_nsmul, exp_neg]
  rw [this]
  exact (tendsto_exp_mul_div_rpow_atTop s (1 / 2) one_half_pos).inv_tendsto_atTop

theorem GammaIntegral_convergent {s : ℝ} (h : 0 < s) :
    IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    refine IntegrableOn.continuousOn_mul continuousOn_id.neg.rexp ?_ isCompact_Icc
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp ?_
    exact intervalIntegrable_rpow' (by linarith)
  · refine integrable_of_isBigO_exp_neg one_half_pos ?_ (Gamma_integrand_isLittleO _).isBigO
    exact continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind))

end Real

namespace Complex

theorem GammaIntegral_convergent {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x => (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) := by
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuous_ofReal.comp continuous_neg.rexp).continuousOn.mul
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have : ContinuousAt (fun x : ℂ => x ^ (s - 1)) ↑x :=
      continuousAt_cpow_const <| ofReal_mem_slitPlane.2 hx
    exact ContinuousAt.comp this continuous_ofReal.continuousAt
  · rw [← hasFiniteIntegral_norm_iff]
    refine HasFiniteIntegral.congr (Real.GammaIntegral_convergent hs).2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_of_nonneg <| le_of_lt <| exp_pos <| -x,
      norm_cpow_eq_rpow_re_of_pos hx _]
    simp

def GammaIntegral (s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ↑(-x).exp * ↑x ^ (s - 1)

set_option backward.isDefEq.respectTransparency false in

theorem GammaIntegral_conj (s : ℂ) : GammaIntegral (conj s) = conj (GammaIntegral s) := by
  rw [GammaIntegral, GammaIntegral, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  dsimp only
  rw [map_mul, conj_ofReal, cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), ← exp_conj, map_mul,
    ← ofReal_log (le_of_lt hx), conj_ofReal, map_sub, map_one]

theorem GammaIntegral_ofReal (s : ℝ) :
    GammaIntegral ↑s = ↑(∫ x : ℝ in Ioi 0, Real.exp (-x) * x ^ (s - 1)) := by
  have : ∀ r : ℝ, Complex.ofReal r = @RCLike.ofReal ℂ _ r := fun r => rfl
  rw [GammaIntegral]
  conv_rhs => rw [this, ← _root_.integral_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx; dsimp only
  conv_rhs => rw [← this]
  rw [ofReal_mul, ofReal_cpow (mem_Ioi.mp hx).le]
  simp
