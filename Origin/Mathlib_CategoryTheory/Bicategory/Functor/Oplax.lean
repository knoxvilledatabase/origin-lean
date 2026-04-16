/-
Extracted from CategoryTheory/Bicategory/Functor/Oplax.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
import Mathlib.Tactic.CategoryTheory.ToApp

noncomputable section

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B ⟶ C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.OplaxFunctor B C` : an oplax functor between bicategories `B` and `C`
* `CategoryTheory.OplaxFunctor.comp F G` : the composition of oplax functors

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

structure OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the oplax unity constraint. -/
  mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  /-- The 2-morphism underlying the oplax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  /-- Naturality of the oplax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g := by
    aesop_cat
  /-- Naturality of the lax functoriality constraight, on the right. -/
  mapComp_naturality_right :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    aesop_cat
  /-- Oplax associativity. -/
  map₂_associator :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
    mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
    aesop_cat
  /-- Oplax left unity. -/
  map₂_leftUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (λ_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (λ_ (map f)).hom := by
    aesop_cat
  /-- Oplax right unity. -/
  map₂_rightUnitor :
    ∀ {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    aesop_cat

initialize_simps_projections OplaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace OplaxFunctor

attribute [reassoc (attr := simp), to_app (attr := simp)]
  mapComp_naturality_left mapComp_naturality_right map₂_associator

attribute [simp, reassoc, to_app] map₂_leftUnitor map₂_rightUnitor

section

variable (F : OplaxFunctor B C)

@[reassoc, to_app]
lemma mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = F.map₂ (α_ f g h).inv ≫
    F.mapComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom := by
  rw [← F.map₂_associator, ← F.map₂_comp_assoc]
  simp

@[simps]
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : OplaxFunctor B B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

instance : Inhabited (OplaxFunctor B B) :=
  ⟨id B⟩

def comp (F : OplaxFunctor B C) (G : OplaxFunctor C D) : OplaxFunctor B D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [← G.map₂_comp_assoc, mapComp_naturality_left, G.map₂_comp_assoc, mapComp_naturality_left,
      assoc]
  mapComp_naturality_right := fun η => by
    dsimp
    intros
    rw [← G.map₂_comp_assoc, mapComp_naturality_right, G.map₂_comp_assoc,
      mapComp_naturality_right, assoc]
  map₂_associator := fun f g h => by
    dsimp
    simp only [map₂_associator, ← PrelaxFunctor.map₂_comp_assoc, ← mapComp_naturality_right_assoc,
      Bicategory.whiskerLeft_comp, assoc]
    simp only [map₂_associator, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_right_assoc,
      Bicategory.whiskerLeft_comp, assoc]

structure PseudoCore (F : OplaxFunctor B C) where
  /-- The isomorphism giving rise to the oplax unity constraint -/
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  /-- The isomorphism giving rise to the oplax functoriality constraint -/
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  /-- `mapIdIso` gives rise to the oplax unity constraint -/
  mapIdIso_hom : ∀ {a : B}, (mapIdIso a).hom = F.mapId a := by aesop_cat
  /-- `mapCompIso` gives rise to the oplax functoriality constraint -/
  mapCompIso_hom :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g := by aesop_cat

attribute [simp] PseudoCore.mapIdIso_hom PseudoCore.mapCompIso_hom

end

end OplaxFunctor

end

end CategoryTheory
