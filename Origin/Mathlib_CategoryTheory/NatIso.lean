/-
Extracted from CategoryTheory/NatIso.lean
Genuine: 21 | Conflates: 0 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Iso

noncomputable section

/-!
# Natural isomorphisms

For the most part, natural isomorphisms are just another sort of isomorphism.

We provide some special support for extracting components:
* if `α : F ≅ G`, then `a.app X : F.obj X ≅ G.obj X`,
and building natural isomorphisms from components:
*
```
NatIso.ofComponents
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f) :
F ≅ G
```
only needing to check naturality in one direction.

## Implementation

Note that `NatIso` is a namespace without a corresponding definition;
we put some declarations that are specifically about natural isomorphisms in the `Iso`
namespace so that they are available using dot notation.
-/

open CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃}
  [Category.{v₃} E]

namespace Iso

@[simps]
def app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X
  hom_inv_id := by rw [← comp_app, Iso.hom_inv_id]; rfl
  inv_hom_id := by rw [← comp_app, Iso.inv_hom_id]; rfl

@[reassoc (attr := simp)]
theorem hom_inv_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.hom.app X ≫ α.inv.app X = 𝟙 (F.obj X) :=
  congr_fun (congr_arg NatTrans.app α.hom_inv_id) X

@[reassoc (attr := simp)]
theorem inv_hom_id_app {F G : C ⥤ D} (α : F ≅ G) (X : C) :
    α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X) :=
  congr_fun (congr_arg NatTrans.app α.inv_hom_id) X

end Iso

namespace NatIso

open CategoryTheory.Category CategoryTheory.Functor

variable {F G : C ⥤ D}

instance hom_app_isIso (α : F ≅ G) (X : C) : IsIso (α.hom.app X) :=
  ⟨⟨α.inv.app X,
    ⟨by rw [← comp_app, Iso.hom_inv_id, ← id_app], by rw [← comp_app, Iso.inv_hom_id, ← id_app]⟩⟩⟩

instance inv_app_isIso (α : F ≅ G) (X : C) : IsIso (α.inv.app X) :=
  ⟨⟨α.hom.app X,
    ⟨by rw [← comp_app, Iso.inv_hom_id, ← id_app], by rw [← comp_app, Iso.hom_inv_id, ← id_app]⟩⟩⟩

section

/-!
Unfortunately we need a separate set of cancellation lemmas for components of natural isomorphisms,
because the `simp` normal form is `α.hom.app X`, rather than `α.app.hom X`.

(With the later, the morphism would be visibly part of an isomorphism, so general lemmas about
isomorphisms would apply.)

In the future, we should consider a redesign that changes this simp norm form,
but for now it breaks too many proofs.
-/

variable (α : F ≅ G)

@[simp]
theorem cancel_natIso_hom_left {X : C} {Z : D} (g g' : G.obj X ⟶ Z) :
    α.hom.app X ≫ g = α.hom.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[simp]
theorem cancel_natIso_inv_left {X : C} {Z : D} (g g' : F.obj X ⟶ Z) :
    α.inv.app X ≫ g = α.inv.app X ≫ g' ↔ g = g' := by simp only [cancel_epi, refl]

@[simp]
theorem cancel_natIso_hom_right {X : D} {Y : C} (f f' : X ⟶ F.obj Y) :
    f ≫ α.hom.app Y = f' ≫ α.hom.app Y ↔ f = f' := by simp only [cancel_mono, refl]

@[simp]
theorem cancel_natIso_inv_right {X : D} {Y : C} (f f' : X ⟶ G.obj Y) :
    f ≫ α.inv.app Y = f' ≫ α.inv.app Y ↔ f = f' := by simp only [cancel_mono, refl]

@[simp]
theorem cancel_natIso_hom_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ F.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ F.obj Y) :
    f ≫ g ≫ α.hom.app Y = f' ≫ g' ≫ α.hom.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

@[simp]
theorem cancel_natIso_inv_right_assoc {W X X' : D} {Y : C} (f : W ⟶ X) (g : X ⟶ G.obj Y)
    (f' : W ⟶ X') (g' : X' ⟶ G.obj Y) :
    f ≫ g ≫ α.inv.app Y = f' ≫ g' ≫ α.inv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono, refl]

@[simp]
theorem inv_inv_app {F G : C ⥤ D} (e : F ≅ G) (X : C) : inv (e.inv.app X) = e.hom.app X := by
  aesop_cat

end

variable {X Y : C}

theorem naturality_2 (α : F ≅ G) (f : X ⟶ Y) : α.hom.app X ≫ G.map f ≫ α.inv.app Y = F.map f := by
  simp

@[reassoc (attr := simp)]
theorem naturality_2' (α : F ⟶ G) (f : X ⟶ Y) {_ : IsIso (α.app Y)} :
    α.app X ≫ G.map f ≫ inv (α.app Y) = F.map f := by
  rw [← Category.assoc, ← naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

instance isIso_app_of_isIso (α : F ⟶ G) [IsIso α] (X) : IsIso (α.app X) :=
  ⟨⟨(inv α).app X,
      ⟨congr_fun (congr_arg NatTrans.app (IsIso.hom_inv_id α)) X,
        congr_fun (congr_arg NatTrans.app (IsIso.inv_hom_id α)) X⟩⟩⟩

@[simp]
theorem isIso_inv_app (α : F ⟶ G) {_ : IsIso α} (X) : (inv α).app X = inv (α.app X) := by
  -- Porting note: the next lemma used to be in `ext`, but that is no longer allowed.
  -- We've added an aesop apply rule;
  -- it would be nice to have a hook to run those without aesop warning it didn't close the goal.
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← NatTrans.comp_app]
  simp

@[simp]
theorem inv_map_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
    inv ((F.map e.inv).app Z) = (F.map e.hom).app Z := by
  aesop_cat

@[simps]
def ofComponents (app : ∀ X : C, F.obj X ≅ G.obj X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y),
      F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f := by aesop_cat) :
    F ≅ G where
  hom := { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv,
      naturality := fun X Y f => by
        have h := congr_arg (fun f => (app X).inv ≫ f ≫ (app Y).inv) (naturality f).symm
        simp only [Iso.inv_hom_id_assoc, Iso.hom_inv_id, assoc, comp_id, cancel_mono] at h
        exact h }

@[simp]
theorem ofComponents.app (app' : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (X) :
    (ofComponents app' naturality).app X = app' X := by aesop

theorem isIso_of_isIso_app (α : F ⟶ G) [∀ X : C, IsIso (α.app X)] : IsIso α :=
  (ofComponents (fun X => asIso (α.app X)) (by aesop)).isIso_hom

@[simps]
def hcomp {F G : C ⥤ D} {H I : D ⥤ E} (α : F ≅ G) (β : H ≅ I) : F ⋙ H ≅ G ⋙ I := by
  refine ⟨α.hom ◫ β.hom, α.inv ◫ β.inv, ?_, ?_⟩
  · ext
    rw [← NatTrans.exchange]
    simp
  ext; rw [← NatTrans.exchange]; simp

theorem isIso_map_iff {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {X Y : C} (f : X ⟶ Y) :
    IsIso (F₁.map f) ↔ IsIso (F₂.map f) := by
  revert F₁ F₂
  suffices ∀ {F₁ F₂ : C ⥤ D} (_ : F₁ ≅ F₂) (_ : IsIso (F₁.map f)), IsIso (F₂.map f) by
    exact fun F₁ F₂ e => ⟨this e, this e.symm⟩
  intro F₁ F₂ e hf
  refine IsIso.mk ⟨e.inv.app Y ≫ inv (F₁.map f) ≫ e.hom.app X, ?_, ?_⟩
  · simp only [NatTrans.naturality_assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app]
  · simp only [assoc, ← e.hom.naturality, IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app]

end NatIso

lemma NatTrans.isIso_iff_isIso_app {F G : C ⥤ D} (τ : F ⟶ G) :
    IsIso τ ↔ ∀ X, IsIso (τ.app X) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ NatIso.isIso_of_isIso_app _⟩

namespace Functor

variable (F : C ⥤ D) (obj : C → D) (e : ∀ X, F.obj X ≅ obj X)

@[simps obj]
def copyObj : C ⥤ D where
  obj := obj
  map f := (e _).inv ≫ F.map f ≫ (e _).hom

@[simps!]
def isoCopyObj : F ≅ F.copyObj obj e :=
  NatIso.ofComponents e (by simp [Functor.copyObj])

end Functor

end CategoryTheory
