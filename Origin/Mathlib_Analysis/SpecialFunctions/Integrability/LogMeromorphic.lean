/-
Extracted from Analysis/SpecialFunctions/Integrability/LogMeromorphic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integrability for Logarithms of Meromorphic Functions

We establish integrability for functions of the form `log ‖meromorphic‖`. In the real setting, these
functions are interval integrable over every interval of the real line. This implies in particular
that logarithms of trigonometric functions are interval integrable. In the complex setting, the
functions are circle integrable over every circle in the complex plane.
-/

open Filter Interval MeasureTheory MeromorphicOn Metric Real

/-!
## Interval Integrability for Logarithms of Real Meromorphic Functions
-/

section IntervalIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

theorem MeromorphicOn.intervalIntegrable_log_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log ‖f ·‖) volume a b := by
  by_cases t₀ : ∀ u : [[a, b]], meromorphicOrderAt f u ≠ ⊤
  · obtain ⟨g, h₁g, h₂g, h₃g⟩ := hf.extract_zeros_poles t₀
      ((MeromorphicOn.divisor f [[a, b]]).finiteSupport isCompact_uIcc)
    have h₄g := MeromorphicOn.extract_zeros_poles_log h₂g h₃g
    rw [intervalIntegrable_congr_codiscreteWithin
      (h₄g.filter_mono (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc))]
    apply IntervalIntegrable.add
    · apply IntervalIntegrable.finsum
      intro i
      apply IntervalIntegrable.const_mul
      rw [(by ring : a = ((a - i) + i)), (by ring : b = ((b - i) + i))]
      apply IntervalIntegrable.comp_sub_right (f := (log ‖·‖)) _ i
      simp [norm_eq_abs, log_abs]
    · apply ContinuousOn.intervalIntegrable
      apply h₁g.continuousOn.norm.log
      simp_all
  · rw [← hf.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_Icc inf_le_sup)] at t₀
    push Not at t₀
    have : (log ‖f ·‖) =ᶠ[Filter.codiscreteWithin (Ι a b)] 0 := by
      apply Filter.EventuallyEq.filter_mono _ (Filter.codiscreteWithin.mono Set.uIoc_subset_uIcc)
      filter_upwards [hf.meromorphicNFAt_mem_codiscreteWithin,
        Filter.self_mem_codiscreteWithin [[a, b]]] with x h₁x h₂x
      simp only [Pi.zero_apply, log_eq_zero, norm_eq_zero]
      left
      by_contra hCon
      simp_all [← h₁x.meromorphicOrderAt_eq_zero_iff, t₀ ⟨x, h₂x⟩]
    rw [intervalIntegrable_congr_codiscreteWithin this]
    apply Iff.mpr _root_.intervalIntegrable_const_iff
    tauto
