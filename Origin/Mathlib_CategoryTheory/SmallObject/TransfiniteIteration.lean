/-
Extracted from CategoryTheory/SmallObject/TransfiniteIteration.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The transfinite iteration of a successor structure

Given a successor structure `Φ : SuccStruct C`
(see the file `Mathlib/CategoryTheory/SmallObject/Iteration/Basic.lean`)
and a well-ordered type `J`, we define the iteration `Φ.iteration J : C`. It is
defined as the colimit of a functor `Φ.iterationFunctor J : J ⥤ C`.

-/

universe w v u

namespace CategoryTheory.SmallObject.SuccStruct

open Category Limits

variable {C : Type u} [Category.{v} C] (Φ : SuccStruct C)
  (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

variable {J} in

noncomputable def iter (j : J) : Φ.Iteration j := Classical.arbitrary _

noncomputable def iterationFunctor : J ⥤ C where
  obj j := (Φ.iter j).F.obj ⟨j, by simp⟩
  map f := Iteration.mapObj _ _ (leOfHom f) _ _ (leOfHom f)

noncomputable def iteration : C := colimit (Φ.iterationFunctor J)

noncomputable def iterationCocone : Cocone (Φ.iterationFunctor J) :=
  colimit.cocone _
