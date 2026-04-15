/-
Extracted from CategoryTheory/Monoidal/Skeleton.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.

## Main results

* `Skeleton.instMonoid`, for monoidal categories.
* `Skeleton.instCommMonoid`, for braided monoidal categories.

-/

namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

abbrev monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where
  mul X Y := (X ⊗ Y : C)
  one := (𝟙_ C : C)
  one_mul X := hC ⟨λ_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

def commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

noncomputable instance instMonoidalCategory : MonoidalCategory (Skeleton C) :=
  Monoidal.transport (skeletonEquivalence C).symm

noncomputable instance instMonoid : Monoid (Skeleton C) :=
  monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

theorem mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out ⊗ Y.out) := rfl

theorem one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C) := rfl

theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X ⊗ φ Y⟩

noncomputable instance instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C) := by
  letI := braidedCategoryOfFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse
  exact this

noncomputable instance instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C) :=
  commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

end Skeleton

end CategoryTheory
