/-
Extracted from CategoryTheory/Whiskering.lean
Genuine: 19 | Conflates: 0 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful

noncomputable section

/-!
# Whiskering

Given a functor `F : C ⥤ D` and functors `G H : D ⥤ E` and a natural transformation `α : G ⟶ H`,
we can construct a new natural transformation `F ⋙ G ⟶ F ⋙ H`,
called `whiskerLeft F α`. This is the same as the horizontal composition of `𝟙 F` with `α`.

This operation is functorial in `F`, and we package this as `whiskeringLeft`. Here
`(whiskeringLeft.obj F).obj G` is `F ⋙ G`, and
`(whiskeringLeft.obj F).map α` is `whiskerLeft F α`.
(That is, we might have alternatively named this as the "left composition functor".)

We also provide analogues for composition on the right, and for these operations on isomorphisms.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)
We also show these natural isomorphisms satisfy the triangle and pentagon identities.
-/

namespace CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

@[simps]
def whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) :
    F ⋙ G ⟶ F ⋙ H where
  app X := α.app (F.obj X)
  naturality X Y f := by rw [Functor.comp_map, Functor.comp_map, α.naturality]

@[simps]
def whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) :
    G ⋙ F ⟶ H ⋙ F where
  app X := F.map (α.app X)
  naturality X Y f := by
    rw [Functor.comp_map, Functor.comp_map, ← F.map_comp, ← F.map_comp, α.naturality]

variable (C D E)

@[simps]
def whiskeringLeft : (C ⥤ D) ⥤ (D ⥤ E) ⥤ C ⥤ E where
  obj F :=
    { obj := fun G => F ⋙ G
      map := fun α => whiskerLeft F α }
  map τ :=
    { app := fun H =>
        { app := fun c => H.map (τ.app c)
          naturality := fun X Y f => by dsimp; rw [← H.map_comp, ← H.map_comp, ← τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [f.naturality] }

@[simps]
def whiskeringRight : (D ⥤ E) ⥤ (C ⥤ D) ⥤ C ⥤ E where
  obj H :=
    { obj := fun F => F ⋙ H
      map := fun α => whiskerRight α H }
  map τ :=
    { app := fun F =>
        { app := fun c => τ.app (F.obj c)
          naturality := fun X Y f => by dsimp; rw [τ.naturality] }
      naturality := fun X Y f => by ext; dsimp; rw [← NatTrans.naturality] }

variable {C} {D} {E}

instance faithful_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] :
    ((whiskeringRight C D E).obj F).Faithful where
  map_injective hαβ := by
    ext X
    exact F.map_injective <| congr_fun (congr_arg NatTrans.app hαβ) X

@[simps]
def Functor.FullyFaithful.whiskeringRight {F : D ⥤ E} (hF : F.FullyFaithful)
    (C : Type*) [Category C] :
    ((whiskeringRight C D E).obj F).FullyFaithful where
  preimage f :=
    { app := fun X => hF.preimage (f.app X)
      naturality := fun _ _ g => by
        apply hF.map_injective
        dsimp
        simp only [map_comp, map_preimage]
        apply f.naturality }

def whiskeringLeftObjIdIso : (whiskeringLeft C C E).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

def whiskeringLeftObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringLeft C D' E).obj (F ⋙ G) ≅
    (whiskeringLeft D D' E).obj G ⋙ (whiskeringLeft C D E).obj F :=
  Iso.refl _

def wiskeringRightObjIdIso : (whiskeringRight E C C).obj (𝟭 _) ≅ 𝟭 _ :=
  Iso.refl _

def whiskeringRightObjCompIso {D' : Type u₄} [Category.{v₄} D'] (F : C ⥤ D) (G : D ⥤ D') :
    (whiskeringRight E C D).obj F ⋙ (whiskeringRight E D D').obj G ≅
    (whiskeringRight E C D').obj (F ⋙ G) :=
  Iso.refl _

instance full_whiskeringRight_obj {F : D ⥤ E} [F.Faithful] [F.Full] :
    ((whiskeringRight C D E).obj F).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight C).full

@[simp]
theorem whiskerRight_id {G : C ⥤ D} (F : D ⥤ E) :
    whiskerRight (NatTrans.id G) F = NatTrans.id (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp]
theorem whiskerRight_id' {G : C ⥤ D} (F : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F) :=
  ((whiskeringRight C D E).obj F).map_id _

@[simp, reassoc]
theorem whiskerRight_comp {G H K : C ⥤ D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) :
    whiskerRight (α ≫ β) F = whiskerRight α F ≫ whiskerRight β F :=
  ((whiskeringRight C D E).obj F).map_comp α β

def isoWhiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ≅ H) : F ⋙ G ≅ F ⋙ H :=
  ((whiskeringLeft C D E).obj F).mapIso α

def isoWhiskerRight {G H : C ⥤ D} (α : G ≅ H) (F : D ⥤ E) : G ⋙ F ≅ H ⋙ F :=
  ((whiskeringRight C D E).obj F).mapIso α

instance isIso_whiskerLeft (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟶ H) [IsIso α] :
    IsIso (whiskerLeft F α) :=
  (isoWhiskerLeft F (asIso α)).isIso_hom

instance isIso_whiskerRight {G H : C ⥤ D} (α : G ⟶ H) (F : D ⥤ E) [IsIso α] :
    IsIso (whiskerRight α F) :=
  (isoWhiskerRight (asIso α) F).isIso_hom

variable {B : Type u₄} [Category.{v₄} B]

attribute [elab_without_expected_type] whiskerLeft whiskerRight

end

namespace Functor

universe u₅ v₅

variable {A : Type u₁} [Category.{v₁} A]

variable {B : Type u₂} [Category.{v₂} B]

@[simps]
def leftUnitor (F : A ⥤ B) :
    𝟭 A ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

@[simps]
def rightUnitor (F : A ⥤ B) :
    F ⋙ 𝟭 B ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

variable {C : Type u₃} [Category.{v₃} C]

variable {D : Type u₄} [Category.{v₄} D]

@[simps]
def associator (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

theorem triangle (F : A ⥤ B) (G : B ⥤ C) :
    (associator F (𝟭 B) G).hom ≫ whiskerLeft F (leftUnitor G).hom =
      whiskerRight (rightUnitor F).hom G := by aesop_cat

variable {E : Type u₅} [Category.{v₅} E]

variable (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) (K : D ⥤ E)

theorem pentagon :
    whiskerRight (associator F G H).hom K ≫
        (associator F (G ⋙ H) K).hom ≫ whiskerLeft F (associator G H K).hom =
      (associator (F ⋙ G) H K).hom ≫ (associator F G (H ⋙ K)).hom := by aesop_cat

end Functor

end CategoryTheory
