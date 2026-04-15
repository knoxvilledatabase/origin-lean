/-
Extracted from CategoryTheory/Bicategory/NaturalTransformation/Pseudo.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Strong transformations of pseudofunctors

There are three types of transformations between pseudofunctors, depending on the direction
or invertibility of the 2-morphism witnessing the naturality condition.

In this file we define strong transformations, which require the 2-morphism to be invertible.

## Main definitions

* `Pseudofunctor.StrongTrans F G`: strong transformations between pseudofunctors `F` and `G`.
* `Pseudofunctor.StrongTrans.mkOfOplax η`: given a strong transformation `η` between the
  underlying oplax functors, `mkOfOplax` lifts this to a strong transformation between the
  pseudofunctors.
* `Pseudofunctor.StrongTrans.vcomp η θ`: the vertical composition of strong transformations `η`
  and `θ`.

Using this, we obtain a (scoped) `CategoryStruct` on pseudofunctors, where the arrows are given by
strong transformations. To access this instance, run `open scoped Pseudofunctor.StrongTrans`.
See `Pseudofunctor.StrongTrans.categoryStruct`.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory.Pseudofunctor

open Category Bicategory Oplax

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

structure StrongTrans (F G : Pseudofunctor B C) where
  /-- The component 1-morphisms of a strong transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-isomorphisms underlying the strong naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  /-- Naturality of the strong naturality constraint. -/
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    cat_disch
  /-- Oplax unity. -/
  naturality_id (a : B) :
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    cat_disch
  /-- Oplax functoriality. -/
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    cat_disch

attribute [reassoc (attr := simp)] StrongTrans.naturality_naturality

  StrongTrans.naturality_id StrongTrans.naturality_comp

namespace StrongTrans

variable {F G : B ⥤ᵖ C}

set_option backward.isDefEq.respectTransparency false in
