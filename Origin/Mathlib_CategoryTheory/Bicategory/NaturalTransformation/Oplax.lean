/-
Extracted from CategoryTheory/Bicategory/NaturalTransformation/Oplax.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Transformations between oplax functors

Just as there are natural transformations between functors, there are transformations
between oplax functors. The equality in the naturality condition of a natural transformation gets
replaced by a specified 2-morphism. Now, there are three possible types of transformations (between
oplax functors):
* oplax natural transformations;
* lax natural transformations;
* strong natural transformations.

These differ in the direction (and invertibility) of the 2-morphisms involved in the naturality
condition.

## Main definitions

* `Oplax.LaxTrans F G`: lax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `app a ≫ G.map f ⟶ F.map f ≫ app b` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.OplaxTrans F G`: oplax transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.
* `Oplax.StrongTrans F G`: strong transformations between oplax functors `F` and `G`. The naturality
  condition is given by a 2-isomorphism `F.map f ≫ app b ≅ app a ≫ G.map f` for each 1-morphism
  `f : a ⟶ b`.

Using these, we define three (scoped) `CategoryStruct` instances on `B ⥤ᵒᵖᴸ C`, in the
`Oplax.LaxTrans`, `Oplax.OplaxTrans`, and `Oplax.StrongTrans` namespaces. The arrows in these
`CategoryStruct` instances are given by lax transformations, oplax transformations, and strong
transformations respectively.

We also provide API for going between oplax transformations and strong transformations:
* `OplaxTrans.StrongCore η`: a structure on an oplax transformation between oplax functors that
  promotes it to a strong transformation.
* `StrongTrans.mkOfOplax η η'`: given an oplax transformation `η` such that each component
  2-morphism is an isomorphism, `mkOfOplax` gives the corresponding strong transformation.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory.Oplax

open Category Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

structure LaxTrans (F G : OplaxFunctor B C) where
  /-- The component 1-morphisms of a lax transformation. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-morphisms underlying the lax naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : app a ≫ G.map f ⟶ F.map f ≫ app b
  naturality_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
      naturality f ≫ F.map₂ η ▷ app b = app a ◁ G.map₂ η ≫ naturality g := by
    cat_disch
  naturality_id (a : B) :
      naturality (𝟙 a) ≫ F.mapId a ▷ app a =
        app a ◁ G.mapId a ≫ (ρ_ (app a)).hom ≫ (λ_ (app a)).inv := by
    cat_disch
  naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
      naturality (f ≫ g) ≫ F.mapComp f g ▷ app c =
        app a ◁ G.mapComp f g ≫ (α_ _ _ _).inv ≫
          naturality f ▷ G.map g ≫ (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv := by
    cat_disch

namespace LaxTrans

attribute [reassoc (attr := simp)] naturality_naturality naturality_id naturality_comp

variable {F G H : OplaxFunctor B C}

variable (η : LaxTrans F G) (θ : LaxTrans G H)

variable (F) in

def id : LaxTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv

-- INSTANCE (free from Core): :

abbrev vCompApp (a : B) : F.obj a ⟶ H.obj a :=
  η.app a ≫ θ.app a

abbrev vCompNaturality {a b : B} (f : a ⟶ b) :
    (η.app a ≫ θ.app a) ≫ H.map f ⟶ F.map f ≫ η.app b ≫ θ.app b :=
  (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv ≫
    η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom

theorem vComp_naturality_naturality {a b : B} {f g : a ⟶ b} (β : f ⟶ g) :
    η.vCompNaturality θ f ≫ F.map₂ β ▷ η.vCompApp θ b =
      η.vCompApp θ a ◁ H.map₂ β ≫ η.vCompNaturality θ g :=
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality f ⊗≫
          (η.naturality f ≫ F.map₂ β ▷ η.app b) ▷ θ.app b ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality f ≫ G.map₂ β ▷ θ.app b) ⊗≫
          η.naturality g ▷ θ.app b ⊗≫ 𝟙 _ := by
      rw [naturality_naturality]
      bicategory
    _ = _ := by
      rw [naturality_naturality]
      bicategory

theorem vComp_naturality_id (a : B) :
    η.vCompNaturality θ (𝟙 a) ≫ F.mapId a ▷ η.vCompApp θ a =
      η.vCompApp θ a ◁ H.mapId a ≫ (ρ_ (η.vCompApp θ a)).hom ≫ (λ_ (η.vCompApp θ a)).inv := by
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality (𝟙 a) ⊗≫
          (η.naturality (𝟙 a) ≫ F.mapId a ▷ η.app a) ▷ θ.app a ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality (𝟙 a) ≫ G.mapId a ▷ θ.app a) ⊗≫ 𝟙 _ := by
      rw [η.naturality_id]
      bicategory
    _ = _ := by
      rw [θ.naturality_id]
      bicategory

theorem vComp_naturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    η.vCompNaturality θ (f ≫ g) ≫ F.mapComp f g ▷ η.vCompApp θ c =
      η.vCompApp θ a ◁ H.mapComp f g ≫
        (α_ (η.vCompApp θ a) (H.map f) (H.map g)).inv ≫
          η.vCompNaturality θ f ▷ H.map g ≫
            (α_ (F.map f) (η.vCompApp θ b) (H.map g)).hom ≫
              F.map f ◁ η.vCompNaturality θ g ≫ (α_ (F.map f) (F.map g) (η.vCompApp θ c)).inv := by
  calc
    _ = 𝟙 _ ⊗≫ η.app a ◁ θ.naturality (f ≫ g) ⊗≫
          (η.naturality (f ≫ g) ≫ F.mapComp f g ▷ η.app c) ▷ θ.app c ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.naturality (f ≫ g) ≫ G.mapComp f g ▷ θ.app c) ⊗≫
          (η.naturality f ▷ G.map g ⊗≫ F.map f ◁ η.naturality g) ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [η.naturality_comp]
      bicategory
    _ = 𝟙 _ ⊗≫ η.app a ◁ (θ.app a ◁ H.mapComp f g ⊗≫ θ.naturality f ▷ H.map g) ⊗≫
          ((η.app a ≫ G.map f) ◁ θ.naturality g ≫ η.naturality f ▷ (G.map g ≫ θ.app c)) ⊗≫
            F.map f ◁ η.naturality g ▷ θ.app c ⊗≫ 𝟙 _ := by
      rw [θ.naturality_comp]
      bicategory
    _ = _ := by
      rw [whisker_exchange]
      bicategory

def vComp (η : LaxTrans F G) (θ : LaxTrans G H) : LaxTrans F H where
  app a := vCompApp η θ a
  naturality := vCompNaturality η θ
  naturality_naturality := vComp_naturality_naturality η θ
  naturality_id := vComp_naturality_id η θ
  naturality_comp := vComp_naturality_comp η θ

attribute [local simp] vCompApp vCompNaturality in
