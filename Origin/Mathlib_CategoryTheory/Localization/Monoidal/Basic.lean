/-
Extracted from CategoryTheory/Localization/Monoidal/Basic.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localization of monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure: this means `W`
is multiplicative and stable by left and right whiskerings (this is
the type class `W.IsMonoidal`). Let `L : C ⥤ D` be a localization functor
for `W`. In the file, we construct a monoidal category structure
on `D` such that the localization functor is monoidal. The structure
is actually defined on a type synonym `LocalizedMonoidal L W ε`.
Here, the data `ε : L.obj (𝟙_ C) ≅ unit` is an isomorphism to some
object `unit : D` which allows the user to provide a preferred choice
of a unit object.

The symmetric case is considered in the file
`Mathlib/CategoryTheory/Localization/Monoidal/Braided.lean`.

-/

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C]

namespace MorphismProperty

class IsMonoidal : Prop extends W.IsMultiplicative where
  whiskerLeft (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)
  whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y)

lemma IsMonoidal.mk' [W.IsMultiplicative]
    (h : ∀ {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (_ : W f) (_ : W g), W (f ⊗ₘ g)) :
    W.IsMonoidal where
  whiskerLeft X _ _ g hg := by simpa using h (𝟙 X) g (W.id_mem _) hg
  whiskerRight f hf Y := by simpa using h f (𝟙 Y) hf (W.id_mem _)

variable [W.IsMonoidal]

lemma whiskerLeft_mem (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g) :=
  IsMonoidal.whiskerLeft _ _ hg

lemma whiskerRight_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) (Y : C) : W (f ▷ Y) :=
  IsMonoidal.whiskerRight _ hf Y

lemma tensorHom_mem {X₁ X₂ : C} (f : X₁ ⟶ X₂) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (hf : W f) (hg : W g) : W (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact comp_mem _ _ _ (whiskerRight_mem _ _ hf _) (whiskerLeft_mem _ _ _ hg)

-- INSTANCE (free from Core): {C'

end MorphismProperty
