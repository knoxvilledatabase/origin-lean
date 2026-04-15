/-
Extracted from CategoryTheory/Monoidal/Comon_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

class ComonObj (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul (X) : comul ≫ counit ▷ X = (λ_ X).inv := by cat_disch
  comul_counit (X) : comul ≫ X ◁ counit = (ρ_ X).inv := by cat_disch
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch

namespace ComonObj
