/-
Extracted from MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean
Genuine: 3 of 6 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Displacement is at most the integral of the speed

In this file we prove several version of the following fact:
the displacement (`dist (f a) (f b)`) is at most the integral of `‖deriv f‖` over `[a, b]`.
-/

open Filter Set MeasureTheory Measure Metric

open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Line

variable {f : ℝ → E} {a b : ℝ}

lemma norm_sub_le_integral_of_norm_deriv_le_of_le {B : ℝ → ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hfB : ∀ᵐ t, t ∈ Ioo a b → ‖deriv f t‖ ≤ B t)
    (hBi : IntervalIntegrable B volume a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, B t := by
  -- WLOG, the codomain is a complete space.
  wlog hE : CompleteSpace E generalizing E
  · set g : ℝ → UniformSpace.Completion E := (↑) ∘ f with hg
    have hgc : ContinuousOn g (Icc a b) :=
      (UniformSpace.Completion.continuous_coe E).comp_continuousOn hfc
    have hgd : DifferentiableOn ℝ g (Ioo a b) :=
      UniformSpace.Completion.toComplL.differentiable.comp_differentiableOn hfd
    have hdg t (ht : t ∈ Ioo a b) : deriv g t = deriv f t := by
      have : HasFDerivAt (𝕜 := ℝ) (↑) UniformSpace.Completion.toComplL (f t) := by
        rw [← UniformSpace.Completion.coe_toComplL (𝕜 := ℝ)]
        exact (UniformSpace.Completion.toComplL (E := E) (𝕜 := ℝ)).hasFDerivAt
      have hdft : HasDerivAt f (deriv f t) t := hfd.hasDerivAt <| Ioo_mem_nhds ht.1 ht.2
      rw [hg, (this.comp_hasDerivAt t hdft).deriv, UniformSpace.Completion.coe_toComplL]
    have hgn : ∀ᵐ t, t ∈ Ioo a b → ‖deriv g t‖ ≤ B t :=
      hfB.mono fun t htB ht ↦ by
        simpa only [hdg t ht, UniformSpace.Completion.norm_coe] using htB ht
    simpa [g, ← dist_eq_norm_sub] using this hgc hgd hgn inferInstance
  -- In a complete space, we have
  -- `‖f b - f a‖ = ‖∫ t in a..b, deriv f t‖ ≤ ∫ t in a..b, ‖deriv f t‖`
  have hfB' : (‖deriv f ·‖) ≤ᵐ[volume.restrict (uIoc a b)] B := by
    rwa [uIoc_of_le hab, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, EventuallyLE,
        ae_restrict_iff' measurableSet_Ioo]
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right (f' := deriv f)]
  · apply intervalIntegral.norm_integral_le_of_norm_le hab _ hBi
    rwa [← ae_restrict_iff' measurableSet_Ioc, ← uIoc_of_le hab]
  · rwa [uIcc_of_le hab]
  · rw [min_eq_left hab, max_eq_right hab]
    intro t ht
    exact hfd.hasDerivAt (isOpen_Ioo.mem_nhds ht) |>.hasDerivWithinAt
  · apply hBi.mono_fun (aestronglyMeasurable_deriv _ _)
    exact hfB'.trans <| .of_forall fun _ ↦ le_abs_self _

-- DISSOLVED: norm_sub_le_mul_volume_of_norm_deriv_le_of_le

end Line

section NormedSpace

open AffineMap

variable {f : E → F} {a b : E} {C r : ℝ} {s : Set E}

-- DISSOLVED: norm_sub_le_mul_volume_of_norm_lineDeriv_le

-- DISSOLVED: norm_sub_le_mul_volume_of_norm_fderiv_le

theorem sub_isBigO_norm_rpow_add_one_of_fderiv (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r)) :
    (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  rcases hderiv.exists_pos with ⟨C, hC₀, hC⟩
  rw [Asymptotics.IsBigOWith_def] at hC
  rcases eventually_nhds_iff_ball.mp (hdf.and hC) with ⟨ε, hε₀, hε⟩
  refine .of_bound C ?_
  rw [eventually_nhds_iff_ball]
  refine ⟨ε, hε₀, fun y hy ↦ ?_⟩
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_add_one' (by positivity) (by positivity),
    ← mul_assoc]
  have hsub : closedBall a ‖y - a‖ ⊆ ball a ε :=
    closedBall_subset_ball (mem_ball_iff_norm.mp hy)
  apply (convex_closedBall a ‖y - a‖).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
  · exact fun z hz ↦ (hε z <| hsub hz).1
  · intro z hz
    grw [(hε z <| hsub hz).2, Real.norm_of_nonneg (by positivity), mem_closedBall_iff_norm.mp hz]
  · simp
  · simp [dist_eq_norm_sub]

theorem isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (hr : 0 ≤ r)
    (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x) (hderiv : fderiv ℝ f =O[𝓝 a] (‖· - a‖ ^ r))
    (hf₀ : f a = 0) :
    f =O[𝓝 a] (‖· - a‖ ^ (r + 1)) := by
  simpa [hf₀] using sub_isBigO_norm_rpow_add_one_of_fderiv hr hdf hderiv

end NormedSpace
