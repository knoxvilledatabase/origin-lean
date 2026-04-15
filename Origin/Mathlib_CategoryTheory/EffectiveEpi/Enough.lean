/-
Extracted from CategoryTheory/EffectiveEpi/Enough.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!

# Effectively enough objects in the image of a functor

We define the class `F.EffectivelyEnough` on a functor `F : C ⥤ D` which says that for every object
in `D`, there exists an effective epi to it from an object in the image of `F`.
-/

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

namespace Functor

structure EffectivePresentation (X : D) where
  /-- The object of `C` giving the source of the effective epi -/
  p : C
  /-- The morphism `F.obj p ⟶ X` -/
  f : F.obj p ⟶ X
  /-- `f` is an effective epi -/
  effectiveEpi : EffectiveEpi f

class EffectivelyEnough : Prop where
  /-- For every `X : D`, there exists an object `p` of `C` with an effective epi `F.obj p ⟶ X`. -/
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)

variable [F.EffectivelyEnough]

noncomputable def effectiveEpiOverObj (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

noncomputable def effectiveEpiOver (X : D) : F.effectiveEpiOverObj X ⟶ X :=
  (EffectivelyEnough.presentation X).some.f

instance (X : D) : EffectiveEpi (F.effectiveEpiOver X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

def equivalenceEffectivePresentation (e : C ≌ D) (X : D) :
    EffectivePresentation e.functor X where
  p := e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance

instance [IsEquivalence F] : EffectivelyEnough F where
  presentation X := ⟨equivalenceEffectivePresentation F.asEquivalence X⟩

end Functor

end CategoryTheory
