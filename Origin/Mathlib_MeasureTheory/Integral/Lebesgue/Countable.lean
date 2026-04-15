/-
Extracted from MeasureTheory/Integral/Lebesgue/Countable.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lebesgue integral over finite and countable types, sets and measures

The lemmas in this file require at least one of the following of the Lebesgue integral:
* The type of the set of integration is finite or countable
* The set of integration is finite or countable
* The measure is finite, s-finite or sigma-finite
-/

namespace MeasureTheory

open Set ENNReal NNReal Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section FiniteMeasure

theorem setLIntegral_const_lt_top [IsFiniteMeasure μ] (s : Set α) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    ∫⁻ _ in s, c ∂μ < ∞ := by
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top (μ.restrict s) univ)

theorem lintegral_const_lt_top [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : ∫⁻ _, c ∂μ < ∞ := by
  simpa only [Measure.restrict_univ] using setLIntegral_const_lt_top (univ : Set α) hc

lemma lintegral_eq_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x = c) : ∫⁻ x, f x ∂μ = c := by simp [lintegral_congr_ae hf]

lemma lintegral_le_const [IsProbabilityMeasure μ] {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ c) : ∫⁻ x, f x ∂μ ≤ c :=
  (lintegral_mono_ae hf).trans_eq (by simp)

lemma iInf_le_lintegral [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ⨅ x, f x ≤ ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral f)

lemma lintegral_le_iSup [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ ≤ ⨆ x, f x :=
  le_trans (lintegral_le_iSup_mul f) (by simp)

variable (μ) in

theorem _root_.IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
    [IsFiniteMeasure μ] {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ := by
  rw [← μ.restrict_univ]
  refine setLIntegral_lt_top_of_le_nnreal (measure_ne_top _ _) ?_
  simpa using f_bdd

end FiniteMeasure

section DiracAndCount

theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a := by
  simp [lintegral_congr_ae (ae_eq_dirac' hf)]
