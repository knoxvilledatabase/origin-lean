/-
Extracted from CategoryTheory/Monoidal/Hopf_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of Hopf monoids in a braided monoidal category.


## TODO

* Show that in a Cartesian monoidal category Hopf monoids are exactly group objects.
* Show that `Hopf (ModuleCat R) ≌ HopfAlgCat R`.
-/

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

class HopfObj (X : C) extends BimonObj X where
  /-- The antipode is an endomorphism of the underlying object of the Hopf monoid. -/
  antipode : X ⟶ X
  antipode_left (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by cat_disch
  antipode_right (X) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by cat_disch

namespace HopfObj
