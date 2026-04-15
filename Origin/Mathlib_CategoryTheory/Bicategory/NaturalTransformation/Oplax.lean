/-
Extracted from CategoryTheory/Bicategory/NaturalTransformation/Oplax.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Bicategory.Functor.Oplax

/-!
# Oplax natural transformations

Just as there are natural transformations between functors, there are oplax natural transformations
between oplax functors. The equality in the naturality of natural transformations is replaced by a
specified 2-morphism `F.map f ≫ app b ⟶ app a ≫ G.map f` in the case of oplax natural
transformations.

## Main definitions

* `OplaxNatTrans F G` : oplax natural transformations between oplax functors `F` and `G`
* `OplaxNatTrans.vcomp η θ` : the vertical composition of oplax natural transformations `η`
  and `θ`
* `OplaxNatTrans.category F G` : the category structure on the oplax natural transformations
  between `F` and `G`
-/

namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

structure OplaxNatTrans (F G : OplaxFunctor B C) where
  app (a : B) : F.obj a ⟶ G.obj a
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ⟶ app a ≫ G.map f
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ naturality g = naturality f ≫ app a ◁ G.map₂ η := by
    aesop_cat
  naturality_id :
    ∀ a : B,
      naturality (𝟙 a) ≫ app a ◁ G.mapId a =
        F.mapId a ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      naturality (f ≫ g) ≫ app a ◁ G.mapComp f g =
        F.mapComp f g ▷ app c ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ naturality g ≫ (α_ _ _ _).inv ≫ naturality f ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.app
  CategoryTheory.OplaxNatTrans.naturality
  CategoryTheory.OplaxNatTrans.naturality_naturality
  CategoryTheory.OplaxNatTrans.naturality_id
  CategoryTheory.OplaxNatTrans.naturality_comp

attribute [reassoc (attr := simp)] OplaxNatTrans.naturality_naturality OplaxNatTrans.naturality_id
  OplaxNatTrans.naturality_comp

namespace OplaxNatTrans

section

variable (F : OplaxFunctor B C)

@[simps]
def id : OplaxNatTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {_ _} f := (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv

instance : Inhabited (OplaxNatTrans F F) :=
  ⟨id F⟩

variable {F} {G H : OplaxFunctor B C} (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ θ.naturality h =
      f ◁ θ.naturality g ≫ f ◁ θ.app a ◁ H.map₂ β := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality_naturality]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ η.naturality g ▷ h =
      η.naturality f ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv := by
  rw [← comp_whiskerRight, naturality_naturality, comp_whiskerRight, whisker_assoc]

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ θ.naturality (g ≫ h) ≫ f ◁ θ.app a ◁ H.mapComp g h =
      f ◁ G.mapComp g h ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ θ.naturality h ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ θ.naturality g ▷ H.map h ≫ f ◁ (α_ _ _ _).hom := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality_comp]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    η.naturality (f ≫ g) ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapComp f g ▷ h =
      F.mapComp f g ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ η.naturality g ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                  η.naturality f ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_comp]; simp

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ θ.naturality (𝟙 a) ≫ f ◁ θ.app a ◁ H.mapId a =
      f ◁ G.mapId a ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv := by
  simp_rw [← Bicategory.whiskerLeft_comp, naturality_id]

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    η.naturality (𝟙 a) ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.mapId a ▷ f =
    F.mapId a ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫ (α_ _ _ _).hom := by
  rw [← associator_naturality_middle, ← comp_whiskerRight_assoc, naturality_id]; simp

end

@[simps]
def vcomp (η : OplaxNatTrans F G) (θ : OplaxNatTrans G H) : OplaxNatTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).inv ≫
      η.naturality f ▷ θ.app b ≫ (α_ _ _ _).hom ≫ η.app a ◁ θ.naturality f ≫ (α_ _ _ _).inv
  naturality_comp {a b c} f g := by
    calc
      _ =
          ?_ ≫
            F.mapComp f g ▷ η.app c ▷ θ.app c ≫
              ?_ ≫
                F.map f ◁ η.naturality g ▷ θ.app c ≫
                  ?_ ≫
                    (F.map f ≫ η.app b) ◁ θ.naturality g ≫
                      η.naturality f ▷ (θ.app b ≫ H.map g) ≫
                        ?_ ≫ η.app a ◁ θ.naturality f ▷ H.map g ≫ ?_ :=
        ?_
      _ = _ := ?_
    · exact (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ▷ _ ≫ (α_ _ _ _).hom
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · exact (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv
    · exact _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv
    · rw [whisker_exchange_assoc]
      simp
    · simp

variable (B C)

@[simps id comp]
instance : CategoryStruct (OplaxFunctor B C) where
  Hom := OplaxNatTrans
  id := OplaxNatTrans.id
  comp := OplaxNatTrans.vcomp

end

structure StrongCore {F G : OplaxFunctor B C} (η : OplaxNatTrans F G) where
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ η.app b ≅ η.app a ≫ G.map f
  naturality_hom {a b : B} (f : a ⟶ b) : (naturality f).hom = η.naturality f := by aesop_cat

attribute [nolint docBlame] CategoryTheory.OplaxNatTrans.StrongCore.naturality
  CategoryTheory.OplaxNatTrans.StrongCore.naturality_hom

attribute [simp] StrongCore.naturality_hom

end OplaxNatTrans

end CategoryTheory
