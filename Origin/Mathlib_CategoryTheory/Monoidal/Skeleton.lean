/-
Extracted from CategoryTheory/Monoidal/Skeleton.lean
Genuine: 7 of 18 | Dissolved: 0 | Infrastructure: 11
-/
import Origin.Core

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
  mul X Y := X ⊗ Y
  one := 𝟙_ C
  one_mul X := hC ⟨λ_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

abbrev commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

-- INSTANCE (free from Core): instMonoidalCategory

-- INSTANCE (free from Core): instMonoid

theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X ⊗ᵢ φ Y⟩

-- INSTANCE (free from Core): instBraidedCategory

-- INSTANCE (free from Core): instCommMonoid

end Skeleton

open Functor

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) (e : C ≌ D)

-- INSTANCE (free from Core): [F.LaxMonoidal]

-- INSTANCE (free from Core): [F.OplaxMonoidal]

-- INSTANCE (free from Core): [F.Monoidal]

def Skeletal.monoidHom [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C →* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

noncomputable def Skeleton.monoidHom [F.Monoidal] : Skeleton C →* Skeleton D :=
  (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

def Skeletal.mulEquiv [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

noncomputable def Skeleton.mulEquiv [e.functor.Monoidal] : Skeleton C ≃* Skeleton D :=
  (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

end CategoryTheory
