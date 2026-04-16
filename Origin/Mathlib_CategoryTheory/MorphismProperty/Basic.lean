/-
Extracted from CategoryTheory/MorphismProperty/Basic.lean
Genuine: 51 | Conflates: 0 | Dissolved: 0 | Infrastructure: 24
-/
import Origin.Core
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Order.CompleteBooleanAlgebra

noncomputable section

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsLeft P Q`: `P` respects the property `Q` on the left if `P f → P (i ≫ f)` where
  `i` satisfies `Q`.
* `RespectsRight P Q`: `P` respects the property `Q` on the right if `P f → P (f ≫ i)` where
  `i` satisfies `Q`.
* `Respects`: `P` respects `Q` if `P` respects `Q` both on the left and on the right.

-/

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {D : Type*} [Category D]

def MorphismProperty :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

instance : CompleteBooleanAlgebra (MorphismProperty C) where
  le P₁ P₂ := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f → P₂ f
  __ := inferInstanceAs (CompleteBooleanAlgebra (∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))

instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

variable {C}

namespace MorphismProperty

@[ext]
lemma ext (W W' : MorphismProperty C) (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
    W = W' := by
  funext X Y f
  rw [h]

@[simp]
lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]

@[simp]
def op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun _ _ f => P f.unop

@[simp]
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op

def inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun _ _ f =>
  P (F.map f)

def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

lemma monotone_map (F : C ⥤ D) :
    Monotone (map · F) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

class RespectsRight (P Q : MorphismProperty C) : Prop where
  postcomp {X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f) : P (f ≫ i)

class RespectsLeft (P Q : MorphismProperty C) : Prop where
  precomp {X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f) : P (i ≫ f)

class Respects (P Q : MorphismProperty C) extends P.RespectsLeft Q, P.RespectsRight Q : Prop where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] [P.RespectsRight Q] : P.Respects Q where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] : P.op.RespectsRight Q.op where
  postcomp i hi f hf := RespectsLeft.precomp (Q := Q) i.unop hi f.unop hf

instance (P Q : MorphismProperty C) [P.RespectsRight Q] : P.op.RespectsLeft Q.op where
  precomp i hi f hf := RespectsRight.postcomp (Q := Q) i.unop hi f.unop hf

instance RespectsLeft.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
    [P₂.RespectsLeft Q] : (P₁ ⊓ P₂).RespectsLeft Q where
  precomp i hi f hf := ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩

instance RespectsRight.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
    [P₂.RespectsRight Q] : (P₁ ⊓ P₂).RespectsRight Q where
  postcomp i hi f hf := ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩

variable (C)

def isomorphisms : MorphismProperty C := fun _ _ f => IsIso f

def monomorphisms : MorphismProperty C := fun _ _ f => Mono f

def epimorphisms : MorphismProperty C := fun _ _ f => Epi f

section

variable {C}

abbrev RespectsIso (P : MorphismProperty C) : Prop := P.Respects (isomorphisms C)

lemma RespectsIso.mk (P : MorphismProperty C)
    (hprecomp : ∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z) (_ : P f), P (e.hom ≫ f))
    (hpostcomp : ∀ {X Y Z : C} (e : Y ≅ Z) (f : X ⟶ Y) (_ : P f), P (f ≫ e.hom)) :
    P.RespectsIso where
  precomp e (_ : IsIso e) f hf := hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf

lemma RespectsIso.precomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] (f : Y ⟶ Z) (hf : P f) : P (e ≫ f) :=
  RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf

instance : RespectsIso (⊤ : MorphismProperty C) where
  precomp _ _ _ _ := trivial
  postcomp _ _ _ _ := trivial

lemma RespectsIso.postcomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
    [IsIso e] (f : X ⟶ Y) (hf : P f) : P (f ≫ e) :=
  RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf

instance RespectsIso.op (P : MorphismProperty C) [RespectsIso P] : RespectsIso P.op where
  precomp e (_ : IsIso e) f hf := postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf

instance RespectsIso.unop (P : MorphismProperty Cᵒᵖ) [RespectsIso P] : RespectsIso P.unop where
  precomp e (_ : IsIso e) f hf := postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∃ (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

lemma le_isoClosure (P : MorphismProperty C) : P ≤ P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

instance isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure where
  precomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩

lemma monotone_isoClosure : Monotone (isoClosure (C := C)) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

theorem cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩

theorem cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩

lemma comma_iso_iff (P : MorphismProperty C) [P.RespectsIso] {A B : Type*} [Category A] [Category B]
    {L : A ⥤ C} {R : B ⥤ C} {f g : Comma L R} (e : f ≅ g) :
    P f.hom ↔ P g.hom := by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]

theorem arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

theorem arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  P.arrow_iso_iff e

theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp

lemma isoClosure_eq_iff (P : MorphismProperty C) :
    P.isoClosure = P ↔ P.RespectsIso := by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP ↦ le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

lemma isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] :
    P.isoClosure = P := by rwa [isoClosure_eq_iff]

@[simp]
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure.isoClosure_eq_self

lemma isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] :
    P.isoClosure ≤ Q ↔ P ≤ Q := by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

instance map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨e' ≪≫ e⟩⟩

lemma map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D)
    [RespectsIso Q] :
    P.map F ≤ Q ↔ P ≤ Q.inverseImage F := by
  constructor
  · intro h X Y f hf
    exact h (F.map f) (map_mem_map P F f hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact (Q.arrow_mk_iso_iff e).1 (h _ hf')

@[simp]
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨_, _, f', hf', ⟨F.mapArrow.mapIso e⟩⟩
  · exact monotone_map _ (le_isoClosure P)

lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f hf
    exact P.le_isoClosure _ hf
  · intro X Y f hf
    exact hf

lemma map_id (P : MorphismProperty C) [RespectsIso P] :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure, P.isoClosure_eq_self]

@[simp]
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

instance RespectsIso.inverseImage (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf

lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices ∀ {F G : C ⥤ D} (_ : F ≅ G), P.map F ≤ P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

lemma map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F ≤ P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) [RespectsIso P] (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) [RespectsIso Q] (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q E.symm

lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

end

section

variable {C}

variable {X Y : C} (f : X ⟶ Y)

@[simp]
theorem isomorphisms.iff : (isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
theorem monomorphisms.iff : (monomorphisms C) f ↔ Mono f := by rfl

@[simp]
theorem epimorphisms.iff : (epimorphisms C) f ↔ Epi f := by rfl

theorem isomorphisms.infer_property [hf : IsIso f] : (isomorphisms C) f :=
  hf

theorem monomorphisms.infer_property [hf : Mono f] : (monomorphisms C) f :=
  hf

theorem epimorphisms.infer_property [hf : Epi f] : (epimorphisms C) f :=
  hf

end

instance RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

instance RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

instance RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

def prod {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) :
    MorphismProperty (C₁ × C₂) :=
  fun _ _ f => W₁ f.1 ∧ W₂ f.2

def pi {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
    (W : ∀ j, MorphismProperty (C j)) : MorphismProperty (∀ j, C j) :=
  fun _ _ f => ∀ j, (W j) (f j)

variable {C}

def functorCategory (W : MorphismProperty C) (J : Type*) [Category J] :
    MorphismProperty (J ⥤ C) :=
  fun _ _ f => ∀ (j : J), W (f.app j)

def arrow (W : MorphismProperty C) :
    MorphismProperty (Arrow C) :=
  fun _ _ f => W f.left ∧ W f.right

end MorphismProperty

namespace NatTrans

lemma isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (α.app X) ↔ IsIso (α.app Y) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

end NatTrans

end CategoryTheory
