/-
Extracted from CategoryTheory/Join/Opposites.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Opposites of joins of categories

This file constructs the canonical equivalence of categories `(C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ`.
This equivalence is characterized in both directions.

-/

namespace CategoryTheory.Join

open Opposite Functor

universe v₁ v₂ u₁ u₂

variable (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D]

def opEquiv : (C ⋆ D)ᵒᵖ ≌ Dᵒᵖ ⋆ Cᵒᵖ where
  functor := Functor.leftOp <|
    Join.mkFunctor (inclRight _ _).rightOp (inclLeft _ _).rightOp { app _ := (edge _ _).op }
  inverse := Join.mkFunctor (inclRight _ _).op (inclLeft _ _).op { app _ := (edge _ _).op }
  unitIso := NatIso.ofComponents
    (fun
      | op (left _) => Iso.refl _
      | op (right _) => Iso.refl _)
    (@fun
      | op (left _), op (left _), _ => by cat_disch
      | op (right _), op (left _), _ => by cat_disch
      | op (right _), op (right _), _ => by cat_disch)
  counitIso := NatIso.ofComponents
    (fun
      | left _ => Iso.refl _
      | right _ => Iso.refl _)
  functor_unitIso_comp
    | op (left _) => by cat_disch
    | op (right _) => by cat_disch

variable {C} in
