/-
Extracted from CategoryTheory/Monoidal/Linear.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Linear monoidal categories

A monoidal category is `MonoidalLinear R` if it is monoidal preadditive and
tensor product of morphisms is `R`-linear in both factors.
-/

namespace CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

variable (R : Type*) [Semiring R]

variable (C : Type*) [Category* C] [Preadditive C] [Linear R C]

variable [MonoidalCategory C]

class MonoidalLinear [MonoidalPreadditive C] : Prop where
  whiskerLeft_smul : ∀ (X : C) {Y Z : C} (r : R) (f : Y ⟶ Z), X ◁ (r • f) = r • (X ◁ f) := by
    cat_disch
  smul_whiskerRight : ∀ (r : R) {Y Z : C} (f : Y ⟶ Z) (X : C), (r • f) ▷ X = r • (f ▷ X) := by
    cat_disch

attribute [simp] MonoidalLinear.whiskerLeft_smul MonoidalLinear.smul_whiskerRight

variable {C}

variable [MonoidalPreadditive C] [MonoidalLinear R C]

-- INSTANCE (free from Core): tensorLeft_linear

-- INSTANCE (free from Core): tensorRight_linear

-- INSTANCE (free from Core): tensoringLeft_linear

-- INSTANCE (free from Core): tensoringRight_linear

theorem MonoidalLinear.ofFaithful {D : Type*} [Category* D] [Preadditive D] [Linear R D]
    [MonoidalCategory D] [MonoidalPreadditive D] (F : D ⥤ C) [F.Monoidal] [F.Faithful]
    [F.Linear R] : MonoidalLinear R D :=
  { whiskerLeft_smul := by
      intro X Y Z r f
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerLeft]
      simp
    smul_whiskerRight := by
      intro r X Y f Z
      apply F.map_injective
      rw [Functor.Monoidal.map_whiskerRight]
      simp }
