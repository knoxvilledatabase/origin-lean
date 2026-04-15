/-
Extracted from CategoryTheory/Shift/Quotient.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The shift on a quotient category

Let `C` be a category equipped a shift by a monoid `A`. If we have a relation
on morphisms `r : HomRel C` that is compatible with the shift (i.e. if two
morphisms `f` and `g` are related, then `f⟦a⟧'` and `g⟦a⟧'` are also related
for all `a : A`), then the quotient category `Quotient r` is equipped with
a shift.

The condition `r.IsCompatibleWithShift A` on the relation `r` is a class so that
the shift can be automatically inferred on the quotient category.

-/

universe v v' u u' w

open CategoryTheory Category

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (r : HomRel C) (A : Type w) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace HomRel

class IsCompatibleWithShift : Prop where
  /-- the condition that the relation is preserved by the shift -/
  condition : ∀ (a : A) ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → r (f⟦a⟧') (g⟦a⟧')

end HomRel

namespace CategoryTheory

-- INSTANCE (free from Core): HasShift.quotient

-- INSTANCE (free from Core): Quotient.functor_commShift

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12247

doing so requires `allowUnsafeReducibility`. -/

set_option allowUnsafeReducibility true in

attribute [irreducible] HasShift.quotient Quotient.functor_commShift

namespace Quotient

variable [r.IsCompatibleWithShift A] [F.CommShift A]
    (hF : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)

namespace LiftCommShift

variable {A}

noncomputable def iso (a : A) :
    shiftFunctor (Quotient r) a ⋙ lift r F hF ≅ lift r F hF ⋙ shiftFunctor D a :=
  natIsoLift r ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((functor r).commShiftIso a).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (lift.isLift r F hF) ≪≫ F.commShiftIso a ≪≫
    Functor.isoWhiskerRight (lift.isLift r F hF).symm _ ≪≫ Functor.associator _ _ _)

set_option backward.isDefEq.respectTransparency false in
