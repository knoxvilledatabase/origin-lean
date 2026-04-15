/-
Extracted from MeasureTheory/Function/L1Space/HasFiniteIntegral.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Function with finite integral

In this file we define the predicate `HasFiniteIntegral`, which is then used to define the
predicate `Integrable` in the corresponding file.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`.
  Then `HasFiniteIntegral f` means `∫⁻ a, ‖f a‖ₑ < ∞`.

## Tags

finite integral

-/

noncomputable section

open Topology ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε] [ENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

namespace MeasureTheory

/-! ### Some results about the Lebesgue integral involving a normed group -/

lemma lintegral_enorm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by simp only [edist_zero_right]

theorem lintegral_norm_eq_lintegral_edist (f : α → β) :
    ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [ofReal_norm_eq_enorm, edist_zero_right]

theorem lintegral_edist_triangle {f g h : α → β} (hf : AEStronglyMeasurable f μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) ≤ (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

theorem lintegral_enorm_add_left {f : α → ε''} (hf : AEStronglyMeasurable f μ) (g : α → ε') :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_left' hf.enorm _

theorem lintegral_enorm_add_right (f : α → ε') {g : α → ε''} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_right' _ hg.enorm

/-! ### The predicate `HasFiniteIntegral` -/
