/-
Extracted from Analysis/Calculus/ParametricIntervalIntegral.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals. -/

open TopologicalSpace MeasureTheory Filter Metric Set

open scoped Topology Filter Interval

variable {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] {s : Set H} {a b : ℝ} {bound : ℝ → ℝ}

namespace intervalIntegral

nonrec theorem hasFDerivAt_integral_of_dominated_loc_of_lip
    {F : H → ℝ → E} {F' : ℝ → H →L[𝕜] E} {x₀ : H}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lip : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) s)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasFDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lip h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hF_int hF'_meas h_lip
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

nonrec theorem hasFDerivAt_integral_of_dominated_of_fderiv_le
    {F : H → ℝ → E} {F' : H → ℝ → H →L[𝕜] E} {x₀ : H} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasFDerivAt (fun x => F x t) (F' x t) x) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable
  simp only [intervalIntegral_eq_integral_uIoc]
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).const_smul _

nonrec theorem hasDerivAt_integral_of_dominated_loc_of_lip {F : 𝕜 → ℝ → E} {F' : ℝ → E} {x₀ : 𝕜}
    {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lipsch : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) s)
    (bound_integrable : IntervalIntegrable (bound : ℝ → ℝ) μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lipsch h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hF_int hF'_meas h_lipsch
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜} {s : Set 𝕜}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

end intervalIntegral
