/-
Extracted from AlgebraicTopology/SimplicialObject/Op.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The covariant involution of the category of simplicial objects

In this file, we define the covariant involution `SimplicialObject.opFunctor`
of the category of simplicial objects that is induced by the
covariant involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.

-/

universe v

open CategoryTheory

namespace SimplicialObject

variable {C : Type*} [Category.{v} C]

def opFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

def opObjIso {X : SimplicialObject C} {n : SimplexCategoryᵒᵖ} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _
