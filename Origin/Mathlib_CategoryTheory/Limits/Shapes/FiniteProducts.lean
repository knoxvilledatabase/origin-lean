/-
Extracted from CategoryTheory/Limits/Shapes/FiniteProducts.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Categories with finite (co)products

Typeclasses representing categories with (co)products over finite indexing types.
-/

universe w v u

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

class HasFiniteProducts : Prop where
  /-- `C` has finite products -/
  out (n : ℕ) : HasLimitsOfShape (Discrete (Fin n)) C

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): hasLimitsOfShape_discrete

noncomputable example [HasFiniteProducts C] (X : C) : C :=

  ∏ᶜ fun _ : Fin 5 => X

theorem hasFiniteProducts_of_hasProducts [HasProducts.{w} C] : HasFiniteProducts C :=
  ⟨fun _ => hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

class HasFiniteCoproducts : Prop where
  /-- `C` has all finite coproducts -/
  out (n : ℕ) : HasColimitsOfShape (Discrete (Fin n)) C

-- INSTANCE (free from Core): hasColimitsOfShape_discrete

-- INSTANCE (free from Core): (priority

theorem hasFiniteCoproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasFiniteCoproducts C :=
  ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift.{w})⟩

end CategoryTheory.Limits
