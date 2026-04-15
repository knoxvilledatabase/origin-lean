/-
Extracted from MeasureTheory/Group/LIntegral.lean
Genuine: 3 of 4 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Group.Measure

/-!
# Lebesgue Integration on Groups

We develop properties of integrals with a group as domain.
This file contains properties about Lebesgue integration.
-/

namespace MeasureTheory

open Measure TopologicalSpace

open scoped ENNReal

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

section MeasurableMul

variable [Group G] [MeasurableMul G]

@[to_additive
      "Translating a function by left-addition does not change its Lebesgue integral with
      respect to a left-invariant measure."]
theorem lintegral_mul_left_eq_self [IsMulLeftInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (g * x) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulLeft g).symm
  simp [map_mul_left_eq_self μ g]

@[to_additive
      "Translating a function by right-addition does not change its Lebesgue integral with
      respect to a right-invariant measure."]
theorem lintegral_mul_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x * g) ∂μ) = ∫⁻ x, f x ∂μ := by
  convert (lintegral_map_equiv f <| MeasurableEquiv.mulRight g).symm using 1
  simp [map_mul_right_eq_self μ g]

@[to_additive] -- Porting note: was `@[simp]`
theorem lintegral_div_right_eq_self [IsMulRightInvariant μ] (f : G → ℝ≥0∞) (g : G) :
    (∫⁻ x, f (x / g) ∂μ) = ∫⁻ x, f x ∂μ := by
  simp_rw [div_eq_mul_inv, lintegral_mul_right_eq_self f g⁻¹]

end MeasurableMul

section TopologicalGroup

variable [TopologicalSpace G] [Group G] [TopologicalGroup G] [BorelSpace G] [IsMulLeftInvariant μ]

-- DISSOLVED: lintegral_eq_zero_of_isMulLeftInvariant

end TopologicalGroup

end MeasureTheory
