/-
Extracted from CategoryTheory/Monoidal/Subcategory.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Full monoidal subcategories

Given a monoidal category `C` and a property of objects `P : ObjectProperty C`
that is monoidal (i.e. it holds for the unit and is stable by `⊗`),
we can put a monoidal structure on `P.FullSubcategory` (the category
structure is defined in `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `ObjectProperty.Lift`
-/

universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ObjectProperty

class TensorLE (P₁ P₂ Q : ObjectProperty C) : Prop where
  prop_tensor (X₁ X₂ : C) (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ ⊗ X₂)

lemma prop_tensor {P₁ P₂ Q : ObjectProperty C} [TensorLE P₁ P₂ Q]
    {X₁ X₂ : C} (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ ⊗ X₂) :=
  TensorLE.prop_tensor _ _ h₁ h₂

class ContainsUnit (P : ObjectProperty C) : Prop where
  prop_unit : P (𝟙_ C)

lemma prop_unit (P : ObjectProperty C) [ContainsUnit P] : P (𝟙_ C) :=
  ContainsUnit.prop_unit

class IsMonoidal (P : ObjectProperty C) : Prop extends
  ContainsUnit P, TensorLE P P P where

class IsMonoidalClosed (P : ObjectProperty C) [MonoidalClosed C] : Prop where
  prop_ihom (X Y : C) : P X → P Y → P ((ihom X).obj Y) := by cat_disch

lemma prop_ihom (P : ObjectProperty C) [MonoidalClosed C] [P.IsMonoidalClosed]
    {X Y : C} (hX : P X) (hY : P Y) : P ((ihom X).obj Y) :=
  IsMonoidalClosed.prop_ihom _ _ hX hY

variable (P : ObjectProperty C) [P.IsMonoidal]
