/-
Extracted from Geometry/Euclidean/PerpBisector.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Perpendicular bisector of a segment

We define `AffineSubspace.perpBisector p₁ p₂` to be the perpendicular bisector of the segment
`[p₁, p₂]`, as a bundled affine subspace. We also prove that a point belongs to the perpendicular
bisector if and only if it is equidistant from `p₁` and `p₂`, as well as a few linear equations that
define this subspace.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

open Set

open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

noncomputable section

namespace AffineSubspace

variable {c p₁ p₂ : P}

def perpBisector (p₁ p₂ : P) : AffineSubspace ℝ P :=
  mk' (midpoint ℝ p₁ p₂) (LinearMap.ker (innerₛₗ ℝ (p₂ -ᵥ p₁)))

theorem mem_perpBisector_iff_inner_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm

theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, Equiv.pointReflection_apply,
    vsub_midpoint, invOf_eq_inv, ← smul_add, real_inner_smul_left, vadd_vsub_assoc]
  simp

theorem mem_perpBisector_pointReflection_iff_inner_eq_zero :
    c ∈ perpBisector p₁ (Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, midpoint_pointReflection_right,
    Equiv.pointReflection_apply, vadd_vsub_assoc, inner_add_right, add_self_eq_zero,
    ← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev]

theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint ℝ p₁ p₂ ∈ perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]

theorem perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty :=
  ⟨_, midpoint_mem_perpBisector _ _⟩
