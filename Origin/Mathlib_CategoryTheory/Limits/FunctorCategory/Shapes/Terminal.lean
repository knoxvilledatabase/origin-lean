/-
Extracted from CategoryTheory/Limits/FunctorCategory/Shapes/Terminal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Initial and terminal objects in the category of functors

We show that if a functor `F : C ⥤ D` is such that `F.obj X`
is terminal for all `X`, then `F` is a terminal object.

-/

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D]

def isTerminal {F : C ⥤ D} (hF : ∀ (X : C), IsTerminal (F.obj X)) :
    IsTerminal F := by
  refine evaluationJointlyReflectsLimits _
    fun X ↦ IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cone.ext (Iso.refl _)

def isInitial {F : C ⥤ D} (hF : ∀ (X : C), IsInitial (F.obj X)) :
    IsInitial F := by
  refine evaluationJointlyReflectsColimits _
    fun X ↦ IsColimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cocone.ext (Iso.refl _)

end CategoryTheory.Functor
