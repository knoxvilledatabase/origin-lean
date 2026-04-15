/-
Extracted from Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/RingInverseOrder.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order properties of `Ring.inverse` in C⋆-algebras

This file shows that `Ring.inverse` is convex on strictly positive operators.

## Main declarations

* `convexOn_ringInverse`: `Ring.inverse` is convex on strictly positive operators, i.e. the inverse
  is operator convex.
-/

namespace CStarAlgebra

open CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Ring in

public lemma convexOn_ringInverse :
    ConvexOn ℝ {a : A | IsStrictlyPositive a} Ring.inverse := by
  /- We need to prove that `(a • x + b • y)⁻¹ ≤ a • x⁻¹ + b • y⁻¹`. To do this, we define
  `z := x^(-1/2) y x^(-1/2)`. This turns the statement to prove into
  `(a • 1 + b • z)⁻¹ ≤ a • 1⁻¹ + b • z⁻¹`, and this can be proven since everything now commutes. -/
  refine ⟨by grind [convex_iff_forall_pos], ?_⟩
  intro x (xpos : IsStrictlyPositive x) y (ypos : IsStrictlyPositive y) a b ha hb hab
  let z := conjSqrt x⁻¹ʳ y
  have zpos : IsStrictlyPositive z := by grind
  have xinvpos : IsStrictlyPositive x⁻¹ʳ := by grind
  have hsp : IsStrictlyPositive (a • 1 + b • z) := by
    by_cases ha' : 0 < a <;> grind [smul_nonneg]
  have h₁ : (a • 1 + b • z) ^ (-1 : ℝ) = cfc (fun r => (a + b * r) ^ (-1 : ℝ)) z := by
    rw [← cfc_smul_id (R := ℝ) (S := ℝ) b z, ← Algebra.algebraMap_eq_smul_one,
        ← cfc_const_add a (fun r => b • r) z]
    simp only [smul_eq_mul]
    refine cfc_rpow fun r hr => ?_
    by_cases ha' : a = 0
    · have hb' : b = 1 := by grind
      simp only [ha', hb', one_mul, zero_add, gt_iff_lt]
      grind
    · grind [add_pos_of_pos_of_nonneg, mul_nonneg]
  have h₂ : (a • 1 + b • z ^ (-1 : ℝ)) = cfc (fun r => (a + b * r ^ (-1 : ℝ))) z := by
    rw [CFC.rpow_eq_cfc_real zpos.nonneg]
    have hcont : ContinuousOn (fun r : ℝ => (r ^ (-1 : ℝ))) (spectrum ℝ z) :=
      ContinuousOn.rpow_const (f := id) (by fun_prop) (by grind)
    rw [← cfc_smul b _ z hcont, ← Algebra.algebraMap_eq_smul_one, ← cfc_const_add a _ z]
    refine cfc_congr fun r hr => ?_
    simp
  calc _ = (a • conjSqrt x 1 + b • conjSqrt x z)⁻¹ʳ := by
        rw [conjSqrt_conjSqrt_ringInverse _ _ xpos, conjSqrt_one x xpos.nonneg]
      _ = (conjSqrt x (a • 1 + b • z))⁻¹ʳ := by simp
      _ = conjSqrt x⁻¹ʳ ((a • 1 + b • z) ^ (-1 : ℝ)) := by
        rw [ringInverse_conjSqrt _ _ xpos, ← inverse_eq_rpow_neg_one]
      _ ≤ conjSqrt x⁻¹ʳ (a • 1 + b • z ^ (-1 : ℝ)) := by
        gcongr
        rw [h₁, h₂]
        refine (cfc_le_iff _ _ _ ?_ ?_).mpr ?_
        · apply ContinuousOn.rpow_const (by fun_prop)
          intro r hr
          have := zpos.spectrum_pos hr
          have : 0 ≤ b * r := by positivity
          cases lt_or_eq_of_le ha <;> grind
        · refine ContinuousOn.const_add (ContinuousOn.const_mul ?_ _) _
          exact ContinuousOn.rpow_const (by fun_prop) (by grind)
        · intro r hr
          suffices (a • 1 + b • r) ^ (-1 : ℤ) ≤ a • 1 ^ (-1 : ℤ) + b • r ^ (-1 : ℤ) by
            simp_rw [← Real.rpow_intCast] at this
            simpa using this
          have : ConvexOn ℝ (Set.Ioi 0) (fun z : ℝ => z ^ (-1 : ℤ)) := convexOn_zpow (-1)
          grind [ConvexOn, IsStrictlyPositive.spectrum_pos]
      _ = conjSqrt x⁻¹ʳ (a • 1 + b • z⁻¹ʳ) := by rw [← inverse_eq_rpow_neg_one]
      _ = a • inverse x + b • conjSqrt x⁻¹ʳ z⁻¹ʳ := by
        simp [conjSqrt_one x⁻¹ʳ (by grind)]
      _ = _ := by
        rw [← ringInverse_conjSqrt _ _ xpos, conjSqrt_conjSqrt_ringInverse _ _ xpos]

end CStarAlgebra
