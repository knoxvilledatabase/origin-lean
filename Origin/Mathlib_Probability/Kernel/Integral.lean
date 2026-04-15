/-
Extracted from Probability/Kernel/Integral.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bochner integrals of kernels

-/

open MeasureTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : β → E} {a : α}

namespace Kernel

lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x ↦ (κ x).real s) μ := by
  refine Integrable.mono' (integrable_const κ.bound.toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact ENNReal.toReal_mono (Kernel.bound_ne_top _) (Kernel.measure_le_bound _ _ _)

lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x).real s) μ :=
  IsFiniteKernel.integrable μ κ hs

lemma integral_congr_ae₂ {f g : α → β → E} {μ : Measure α} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

lemma integral_indicator₂ (f : α → β → E) (s : Set α) (a : α) :
    ∫ y, s.indicator (f · y) a ∂κ a = s.indicator (fun x ↦ ∫ y, f x y ∂κ x) a := by
  by_cases ha : a ∈ s <;> simp [ha]

section Deterministic

variable [CompleteSpace E] {g : α → β}

theorem integral_deterministic' (hg : Measurable g) (hf : StronglyMeasurable f) :
    ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac' _ _ hf]
