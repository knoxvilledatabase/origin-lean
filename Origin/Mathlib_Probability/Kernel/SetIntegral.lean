/-
Extracted from Probability/Kernel/SetIntegral.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Integral against a kernel over a set

This file contains lemmas about the integral against a kernel and over a set.

-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {X Y E : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Kernel X Y)

lemma integral_integral_indicator (μ : Measure X) (f : X → Y → E) {s : Set X}
    (hs : MeasurableSet s) :
    ∫ x, ∫ y, s.indicator (f · y) x ∂κ x ∂μ = ∫ x in s, ∫ y, f x y ∂κ x ∂μ := by
  simp_rw [← integral_indicator hs, Kernel.integral_indicator₂]

end ProbabilityTheory.Kernel
