/-
Extracted from CategoryTheory/Adjunction/Parametrized.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunctions with a parameter

Given bifunctors `F : C₁ ⥤ C₂ ⥤ C₃` and `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`,
this file introduces the notation `F ⊣₂ G` for the adjunctions
with a parameter (in `C₁`) between `F` and `G`.

(See `MonoidalClosed.internalHomAdjunction₂` in the file
`CategoryTheory.Closed.Monoidal` for an example of such an adjunction.)

Note: this notion is weaker than the notion of
"adjunction of two variables" which appears in the mathematical literature.
In order to have an adjunction of two variables, we need
a third functor `H : C₂ᵒᵖ ⥤ C₃ ⥤ C₁` and two adjunctions with
a parameter `F ⊣₂ G` and `F.flip ⊣₂ H`.

## TODO

Show that given `F : C₁ ⥤ C₂ ⥤ C₃`, if `F.obj X₁` has a right adjoint
`G X₁ : C₃ ⥤ C₂` for any `X₁ : C₁`, then `G` extends as a
bifunctor `G' : C₁ᵒᵖ ⥤ C₃ ⥤ C₂` with `F ⊣₂ G'` (and similarly for
left adjoints).

## References
* https://ncatlab.org/nlab/show/two-variable+adjunction

-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

structure ParametrizedAdjunction where
  /-- a family of adjunctions -/
  adj (X₁ : C₁) : F.obj X₁ ⊣ G.obj (op X₁)
  unit_whiskerRight_map {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) :
    (adj X₁).unit ≫ whiskerRight (F.map f) _ = (adj Y₁).unit ≫ whiskerLeft _ (G.map f.op) := by
      cat_disch

infixl:15 " ⊣₂ " => ParametrizedAdjunction

namespace ParametrizedAdjunction

attribute [reassoc] unit_whiskerRight_map

variable {F G}
