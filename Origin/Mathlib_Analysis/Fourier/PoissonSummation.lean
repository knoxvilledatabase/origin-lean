/-
Extracted from Analysis/Fourier/PoissonSummation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), ‖f(x + n)‖` is uniformly convergent on `K`.
  See `Real.tsum_eq_tsum_fourier` for this formulation.

These hypotheses are potentially a little awkward to apply, so we also provide the less general but
easier-to-use result `Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`, in which we assume `f` and
`𝓕 f` both decay as `|x| ^ (-b)` for some `b > 1`, and the even more specific result
`SchwartzMap.tsum_eq_tsum_fourierIntegral`, where we assume that `f` is a Schwartz function. -/

noncomputable section

open Function hiding comp_apply

open Set hiding restrict_apply

open Complex

open Real

open TopologicalSpace Filter MeasureTheory Asymptotics

open scoped Real Filter FourierTransform

open ContinuousMap

theorem Real.fourierCoeff_tsum_comp_add {f : C(ℝ, ℂ)}
    (hf : ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (m : ℤ) : fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
      𝓕 (f : ℝ → ℂ) m := by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨((↑) : ℝ → UnitAddCircle), continuous_quotient_mk'⟩
  have neK : ∀ (K : Compacts ℝ) (g : C(ℝ, ℂ)), ‖(e * g).restrict K‖ = ‖g.restrict K‖ := by
    have (x : ℝ) : ‖e x‖ = 1 := (AddCircle.toCircle (-m • x)).norm_coe
    intro K g
    simp_rw [norm_eq_iSup_norm, restrict_apply, mul_apply, norm_mul, this, one_mul]
  have eadd : ∀ (n : ℤ), e.comp (ContinuousMap.addRight n) = e := by
    intro n; ext1 x
    have : Periodic e 1 := Periodic.comp (fun x => AddCircle.coe_add_period 1 x) (fourier (-m))
    simpa only [mul_one] using this.int_mul n x
  -- Now the main argument. First unwind some definitions.
  calc
    fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
        ∫ x in (0 : ℝ)..1, e x * (∑' n : ℤ, f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [fourierCoeff_eq_intervalIntegral _ m 0, div_one, one_smul, zero_add, e, comp_apply,
        coe_mk, Periodic.lift_coe, zsmul_one, smul_eq_mul]
    -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
    _ = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, (e * f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [coe_mul, Pi.mul_apply,
        ← ContinuousMap.tsum_apply (summable_of_locally_summable_norm hf), tsum_mul_left]
    -- Swap sum and integral.
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, (e * f.comp (ContinuousMap.addRight n)) x := by
      refine (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm ?_).symm
      convert hf ⟨uIcc 0 1, isCompact_uIcc⟩ using 1
      exact funext fun n => neK _ _
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, (e * f).comp (ContinuousMap.addRight n) x := by
      simp only [mul_comp] at eadd ⊢
      simp_rw [eadd]
    -- Rearrange sum of interval integrals into an integral over `ℝ`.
    _ = ∫ x, e x * f x := by
      suffices Integrable (e * f) from this.hasSum_intervalIntegral_comp_add_int.tsum_eq
      apply integrable_of_summable_norm_Icc
      convert hf ⟨Icc 0 1, isCompact_Icc⟩ using 1
      simp_rw [mul_comp] at eadd ⊢
      simp_rw [eadd]
      exact funext fun n => neK ⟨Icc 0 1, isCompact_Icc⟩ _
    -- Minor tidying to finish
    _ = 𝓕 (f : ℝ → ℂ) m := by
      rw [fourier_real_eq_integral_exp_smul]
      congr 1 with x : 1
      rw [smul_eq_mul, comp_apply, coe_mk, coe_mk, ContinuousMap.toFun_eq_coe, fourier_coe_apply]
      congr 2
      push_cast
      ring

theorem Real.tsum_eq_tsum_fourier {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle) := by
  let F : C(UnitAddCircle, ℂ) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert h_sum
    exact Real.fourierCoeff_tsum_comp_add h_norm _
  convert (has_pointwise_sum_fourier_series_of_summable this x).tsum_eq.symm using 1
  · simpa only [F, coe_mk, ← QuotientAddGroup.mk_zero, Periodic.lift_coe, zsmul_one, comp_apply,
      coe_addRight, zero_add]
       using (hasSum_apply (summable_of_locally_summable_norm h_norm).hasSum x).tsum_eq
  · simp_rw [← Real.fourierCoeff_tsum_comp_add h_norm, smul_eq_mul, F, coe_mk]
