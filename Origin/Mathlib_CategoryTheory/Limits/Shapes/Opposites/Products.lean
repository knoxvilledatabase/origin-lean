/-
Extracted from CategoryTheory/Limits/Shapes/Opposites/Products.lean
Genuine: 6 of 15 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Products and coproducts in `C` and `Cᵒᵖ`

We construct products and coproducts in the opposite categories.

-/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

variable (X : Type v₂)

-- INSTANCE (free from Core): hasCoproductsOfShape_opposite

theorem hasCoproductsOfShape_of_opposite [HasProductsOfShape X Cᵒᵖ] : HasCoproductsOfShape X C :=
  haveI : HasLimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasLimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasColimitsOfShape_of_hasLimitsOfShape_op

-- INSTANCE (free from Core): hasProductsOfShape_opposite

theorem hasProductsOfShape_of_opposite [HasCoproductsOfShape X Cᵒᵖ] : HasProductsOfShape X C :=
  haveI : HasColimitsOfShape (Discrete X)ᵒᵖ Cᵒᵖ :=
    hasColimitsOfShape_of_equivalence (Discrete.opposite X).symm
  hasLimitsOfShape_of_hasColimitsOfShape_op

-- INSTANCE (free from Core): hasProducts_opposite

theorem hasProducts_of_opposite [HasCoproducts.{v₂} Cᵒᵖ] : HasProducts.{v₂} C := fun X =>
  hasProductsOfShape_of_opposite X

-- INSTANCE (free from Core): hasCoproducts_opposite

theorem hasCoproducts_of_opposite [HasProducts.{v₂} Cᵒᵖ] : HasCoproducts.{v₂} C := fun X =>
  hasCoproductsOfShape_of_opposite X

-- INSTANCE (free from Core): hasFiniteCoproducts_opposite

theorem hasFiniteCoproducts_of_opposite [HasFiniteProducts Cᵒᵖ] : HasFiniteCoproducts C :=
  { out := fun _ => hasCoproductsOfShape_of_opposite _ }

-- INSTANCE (free from Core): hasFiniteProducts_opposite

theorem hasFiniteProducts_of_opposite [HasFiniteCoproducts Cᵒᵖ] : HasFiniteProducts C :=
  { out := fun _ => hasProductsOfShape_of_opposite _ }

section OppositeCoproducts

variable {α : Type*} {Z : α → C}

variable [HasCoproduct Z]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
