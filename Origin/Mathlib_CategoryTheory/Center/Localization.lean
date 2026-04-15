/-
Extracted from CategoryTheory/Center/Localization.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localization of the center of a category

Given a localization functor `L : C ⥤ D` with respect to `W : MorphismProperty C`,
we define a localization map `CatCenter C → CatCenter D` for the centers
of these categories. In case `L` is an additive functor between preadditive
categories, we promote this to a ring morphism `CatCenter C →+* CatCenter D`.

-/

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (r s : CatCenter C) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace CatCenter

noncomputable def localization : CatCenter D :=
  Localization.liftNatTrans L W L L (𝟭 D) (𝟭 D) (Functor.whiskerRight r L)
