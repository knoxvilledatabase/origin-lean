/-
Extracted from CategoryTheory/Monoidal/Braided/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Braided and symmetric monoidal categories

The basic definitions of braided monoidal categories, and symmetric monoidal categories,
as well as braided functors.

## Implementation note

We make `BraidedCategory` another typeclass, but then have `SymmetricCategory` extend this.
The rationale is that we are not carrying any additional data, just requiring a property.

## Future work

* Construct the Drinfeld center of a monoidal category as a braided monoidal category.
* Say something about pseudo-natural transformations.

## References

* [Pavel Etingof, Shlomo Gelaki, Dmitri Nikshych, Victor Ostrik, *Tensor categories*][egno15]

-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

class BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  /-- The braiding natural isomorphism. -/
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  braiding_naturality_right :
    ∀ (X : C) {Y Z : C} (f : Y ⟶ Z),
      X ◁ f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ f ▷ X := by
    cat_disch
  braiding_naturality_left :
    ∀ {X Y : C} (f : X ⟶ Y) (Z : C),
      f ▷ Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
    cat_disch
  /-- The first hexagon identity. -/
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  /-- The second hexagon identity. -/
  hexagon_reverse :
    ∀ X Y Z : C,
      (α_ X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
        (X ◁ (braiding Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((braiding X Z).hom ▷ Y) := by
    cat_disch

attribute [reassoc (attr := simp)]

  BraidedCategory.braiding_naturality_left

  BraidedCategory.braiding_naturality_right

attribute [reassoc] BraidedCategory.hexagon_forward BraidedCategory.hexagon_reverse

open BraidedCategory
