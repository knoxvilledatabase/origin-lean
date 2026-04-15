/-
Extracted from CategoryTheory/Idempotents/Karoubi.lean
Genuine: 22 of 44 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Equivalence

/-!
# The Karoubi envelope of a category

In this file, we define the Karoubi envelope `Karoubi C` of a category `C`.

## Main constructions and definitions

- `Karoubi C` is the Karoubi envelope of a category `C`: it is an idempotent
complete category. It is also preadditive when `C` is preadditive.
- `toKaroubi C : C ⥤ Karoubi C` is a fully faithful functor, which is an equivalence
(`toKaroubiIsEquivalence`) when `C` is idempotent complete.

-/

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category C]

namespace Idempotents

structure Karoubi where
  /-- an object of the underlying category -/
  X : C
  /-- an endomorphism of the object -/
  p : X ⟶ X
  /-- the condition that the given endomorphism is an idempotent -/
  idem : p ≫ p = p := by aesop_cat

namespace Karoubi

variable {C}

attribute [reassoc (attr := simp)] idem

@[ext (iff := false)]
theorem ext {P Q : Karoubi C} (h_X : P.X = Q.X) (h_p : P.p ≫ eqToHom h_X = eqToHom h_X ≫ Q.p) :
    P = Q := by
  cases P
  cases Q
  dsimp at h_X h_p
  subst h_X
  simpa only [mk.injEq, heq_eq_eq, true_and, eqToHom_refl, comp_id, id_comp] using h_p

@[ext]
structure Hom (P Q : Karoubi C) where
  /-- a morphism between the underlying objects -/
  f : P.X ⟶ Q.X
  /-- compatibility of the given morphism with the given idempotents -/
  comm : f = P.p ≫ f ≫ Q.p := by aesop_cat

instance [Preadditive C] (P Q : Karoubi C) : Inhabited (Hom P Q) :=
  ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[reassoc (attr := simp)]
theorem p_comp {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f := by rw [f.comm, ← assoc, P.idem]

@[reassoc (attr := simp)]
theorem comp_p {P Q : Karoubi C} (f : Hom P Q) : f.f ≫ Q.p = f.f := by
  rw [f.comm, assoc, assoc, Q.idem]

@[reassoc]
theorem p_comm {P Q : Karoubi C} (f : Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p := by rw [p_comp, comp_p]

theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    f.f ≫ g.f = P.p ≫ (f.f ≫ g.f) ≫ R.p := by rw [assoc, comp_p, ← assoc, p_comp]

instance : Category (Karoubi C) where
  Hom := Karoubi.Hom
  id P := ⟨P.p, by repeat' rw [P.idem]⟩
  comp f g := ⟨f.f ≫ g.f, Karoubi.comp_proof g f⟩

@[simp]
theorem hom_ext_iff {P Q : Karoubi C} {f g : P ⟶ Q} : f = g ↔ f.f = g.f := by
  constructor
  · intro h
    rw [h]
  · apply Hom.ext

@[ext]
theorem hom_ext {P Q : Karoubi C} (f g : P ⟶ Q) (h : f.f = g.f) : f = g := by
  simpa [hom_ext_iff] using h

@[simp]
theorem comp_f {P Q R : Karoubi C} (f : P ⟶ Q) (g : Q ⟶ R) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp]
theorem id_f {P : Karoubi C} : Hom.f (𝟙 P) = P.p := rfl

theorem id_eq {P : Karoubi C} : 𝟙 P = ⟨P.p, by repeat' rw [P.idem]⟩ := rfl

instance coe : CoeTC C (Karoubi C) :=
  ⟨fun X => ⟨X, 𝟙 X, by rw [comp_id]⟩⟩

theorem coe_X (X : C) : (X : Karoubi C).X = X := rfl

@[simp]
theorem coe_p (X : C) : (X : Karoubi C).p = 𝟙 X := rfl

@[simp]
theorem eqToHom_f {P Q : Karoubi C} (h : P = Q) :
    Karoubi.Hom.f (eqToHom h) = P.p ≫ eqToHom (congr_arg Karoubi.X h) := by
  subst h
  simp only [eqToHom_refl, Karoubi.id_f, comp_id]

end Karoubi

@[simps]
def toKaroubi : C ⥤ Karoubi C where
  obj X := ⟨X, 𝟙 X, by rw [comp_id]⟩
  map f := ⟨f, by simp only [comp_id, id_comp]⟩

instance : (toKaroubi C).Full where map_surjective f := ⟨f.f, rfl⟩

instance : (toKaroubi C).Faithful where
  map_injective := fun h => congr_arg Karoubi.Hom.f h

variable {C}

@[simps add]
instance instAdd [Preadditive C] {P Q : Karoubi C} : Add (P ⟶ Q) where
  add f g := ⟨f.f + g.f, by rw [add_comp, comp_add, ← f.comm, ← g.comm]⟩

@[simps neg]
instance instNeg [Preadditive C] {P Q : Karoubi C} : Neg (P ⟶ Q) where
  neg f := ⟨-f.f, by simpa only [neg_comp, comp_neg, neg_inj] using f.comm⟩

@[simps zero]
instance instZero [Preadditive C] {P Q : Karoubi C} : Zero (P ⟶ Q) where
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩

attribute [nolint simpNF] CategoryTheory.Idempotents.instZero_zero

instance instAddCommGroupHom [Preadditive C] {P Q : Karoubi C} : AddCommGroup (P ⟶ Q) where
  zero_add f := by
    ext
    apply zero_add
  add_zero f := by
    ext
    apply add_zero
  add_assoc f g h' := by
    ext
    apply add_assoc
  add_comm f g := by
    ext
    apply add_comm
  neg_add_cancel f := by
    ext
    apply neg_add_cancel
  zsmul := zsmulRec
  nsmul := nsmulRec

namespace Karoubi

theorem hom_eq_zero_iff [Preadditive C] {P Q : Karoubi C} {f : P ⟶ Q} : f = 0 ↔ f.f = 0 :=
  hom_ext_iff

@[simps]
def inclusionHom [Preadditive C] (P Q : Karoubi C) : AddMonoidHom (P ⟶ Q) (P.X ⟶ Q.X) where
  toFun f := f.f
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem sum_hom [Preadditive C] {P Q : Karoubi C} {α : Type*} (s : Finset α) (f : α → (P ⟶ Q)) :
    (∑ x ∈ s, f x).f = ∑ x ∈ s, (f x).f :=
  map_sum (inclusionHom P Q) f s

end Karoubi

instance [Preadditive C] : Preadditive (Karoubi C) where
  homGroup P Q := by infer_instance

instance [Preadditive C] : Functor.Additive (toKaroubi C) where

open Karoubi

variable (C)

instance : IsIdempotentComplete (Karoubi C) := by
  refine ⟨?_⟩
  intro P p hp
  simp only [hom_ext_iff, comp_f] at hp
  use ⟨P.X, p.f, hp⟩
  use ⟨p.f, by rw [comp_p p, hp]⟩
  use ⟨p.f, by rw [hp, p_comp p]⟩
  simp [hp]

instance [IsIdempotentComplete C] : (toKaroubi C).EssSurj :=
  ⟨fun P => by
    rcases IsIdempotentComplete.idempotents_split P.X P.p P.idem with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    use Y
    exact
      Nonempty.intro
        { hom := ⟨i, by erw [id_comp, ← h₂, ← assoc, h₁, id_comp]⟩
          inv := ⟨e, by erw [comp_id, ← h₂, assoc, h₁, comp_id]⟩ }⟩

instance toKaroubi_isEquivalence [IsIdempotentComplete C] : (toKaroubi C).IsEquivalence where

def toKaroubiEquivalence [IsIdempotentComplete C] : C ≌ Karoubi C :=
  (toKaroubi C).asEquivalence

instance toKaroubiEquivalence_functor_additive [Preadditive C] [IsIdempotentComplete C] :
    (toKaroubiEquivalence C).functor.Additive :=
  (inferInstance : (toKaroubi C).Additive)

namespace Karoubi

variable {C}

@[simps]
def decompId_i (P : Karoubi C) : P ⟶ P.X :=
  ⟨P.p, by rw [coe_p, comp_id, P.idem]⟩

@[simps]
def decompId_p (P : Karoubi C) : (P.X : Karoubi C) ⟶ P :=
  ⟨P.p, by rw [coe_p, id_comp, P.idem]⟩

@[reassoc]
theorem decompId (P : Karoubi C) : 𝟙 P = decompId_i P ≫ decompId_p P := by
  ext
  simp only [comp_f, id_f, P.idem, decompId_i, decompId_p]

theorem decomp_p (P : Karoubi C) : (toKaroubi C).map P.p = decompId_p P ≫ decompId_i P := by
  ext
  simp only [comp_f, decompId_p_f, decompId_i_f, P.idem, toKaroubi_map_f]

theorem decompId_i_toKaroubi (X : C) : decompId_i ((toKaroubi C).obj X) = 𝟙 _ := by
  rfl

theorem decompId_p_toKaroubi (X : C) : decompId_p ((toKaroubi C).obj X) = 𝟙 _ := by
  rfl

theorem decompId_i_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    f ≫ decompId_i Q = decompId_i P ≫ (by exact Hom.mk f.f (by simp)) := by
  aesop_cat

theorem decompId_p_naturality {P Q : Karoubi C} (f : P ⟶ Q) :
    decompId_p P ≫ f = (by exact Hom.mk f.f (by simp)) ≫ decompId_p Q := by
  aesop_cat

@[simp]
theorem zsmul_hom [Preadditive C] {P Q : Karoubi C} (n : ℤ) (f : P ⟶ Q) : (n • f).f = n • f.f :=
  map_zsmul (inclusionHom P Q) n f

end Karoubi

end Idempotents

end CategoryTheory
