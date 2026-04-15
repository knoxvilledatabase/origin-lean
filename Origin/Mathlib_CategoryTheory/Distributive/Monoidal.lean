/-
Extracted from CategoryTheory/Distributive/Monoidal.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Distributive monoidal categories

## Main definitions

A monoidal category `C` with binary coproducts is left distributive if the left tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(X ⊗ Y) ⨿ (X ⊗ Z) ⟶ X ⊗ (Y ⨿ Z)` can be promoted to an isomorphism. We refer to
this isomorphism as the left distributivity isomorphism.

A monoidal category `C` with binary coproducts is right distributive if the right tensor product
preserves binary coproducts. This means that, for all objects `X`, `Y`, and `Z` in `C`,
the cogap map `(Y ⊗ X) ⨿ (Z ⊗ X) ⟶ (Y ⨿ Z) ⊗ X` can be promoted to an isomorphism. We refer to
this isomorphism as the right distributivity isomorphism.

A distributive monoidal category is a monoidal category that is both left and right distributive.

## Main results

- A symmetric monoidal category is left distributive if and only if it is right distributive.

- A closed monoidal category is left distributive.

- For a category `C` the category of endofunctors `C ⥤ C` is left distributive (but almost
  never right distributive). The left distributivity is tantamount to the fact that the coproduct
  in the functor categories is computed pointwise.

- We show that any preadditive monoidal category with coproducts is distributive. This includes the
  examples of abelian groups, R-modules, and vector bundles.

## TODO

Show that a distributive monoidal category whose unit is weakly terminal is finitary distributive.

Show that the category of pointed types with the monoidal structure given by the smash product of
pointed types and the coproduct given by the wedge sum is distributive.

## References

* [Hans-Joachim Baues, Mamuka Jibladze, Andy Tonks, Cohomology of
  monoids in monoidal categories, in: Operads: Proceedings of Renaissance
  Conferences, Contemporary Mathematics 202, AMS (1997) 137-166][MR1268290]

-/

universe v v₂ u u₂

noncomputable section

namespace CategoryTheory

open Category MonoidalCategory Limits Iso

class IsMonoidalLeftDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorLeft (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorLeft X) := by infer_instance

class IsMonoidalRightDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] : Prop where
  preservesBinaryCoproducts_tensorRight (X : C) :
    PreservesColimitsOfShape (Discrete WalkingPair) (tensorRight X) := by infer_instance

class IsMonoidalDistrib (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [HasBinaryCoproducts C] extends
  IsMonoidalLeftDistrib C, IsMonoidalRightDistrib C

variable {C} [Category.{v} C] [MonoidalCategory C] [HasBinaryCoproducts C]

section IsMonoidalLeftDistrib

attribute [instance] IsMonoidalLeftDistrib.preservesBinaryCoproducts_tensorLeft

def leftDistrib [IsMonoidalLeftDistrib C] (X Y Z : C) :
    (X ⊗ Y) ⨿ (X ⊗ Z) ≅ X ⊗ (Y ⨿ Z) :=
  PreservesColimitPair.iso (tensorLeft X) Y Z

end IsMonoidalLeftDistrib

namespace Distributive

scoped notation "∂L" => leftDistrib

end Distributive

open Distributive

lemma IsMonoidalLeftDistrib.of_isIso_coprodComparisonTensorLeft
    [i : ∀ {X Y Z : C}, IsIso (coprodComparison (tensorLeft X) Y Z)] : IsMonoidalLeftDistrib C where
  preservesBinaryCoproducts_tensorLeft X :=
    preservesBinaryCoproducts_of_isIso_coprodComparison (tensorLeft X)
