/-
Extracted from CategoryTheory/Monoidal/Preadditive.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preadditive monoidal categories

A monoidal category is `MonoidalPreadditive` if it is preadditive and tensor product of morphisms
is linear in both factors.
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (C : Type*) [Category* C] [Preadditive C] [MonoidalCategory C]

class MonoidalPreadditive : Prop where
  whiskerLeft_zero : ∀ {X Y Z : C}, X ◁ (0 : Y ⟶ Z) = 0 := by cat_disch
  zero_whiskerRight : ∀ {X Y Z : C}, (0 : Y ⟶ Z) ▷ X = 0 := by cat_disch
  whiskerLeft_add : ∀ {X Y Z : C} (f g : Y ⟶ Z), X ◁ (f + g) = X ◁ f + X ◁ g := by cat_disch
  add_whiskerRight : ∀ {X Y Z : C} (f g : Y ⟶ Z), (f + g) ▷ X = f ▷ X + g ▷ X := by cat_disch

attribute [simp] MonoidalPreadditive.whiskerLeft_zero MonoidalPreadditive.zero_whiskerRight

attribute [simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

variable {C}

variable [MonoidalPreadditive C]

namespace MonoidalPreadditive
