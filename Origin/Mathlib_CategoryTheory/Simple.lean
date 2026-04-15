/-
Extracted from CategoryTheory/Simple.lean
Genuine: 10 | Conflates: 0 | Dissolved: 8 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.Atoms

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop` valued typeclass `Simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

-- DISSOLVED: Simple

-- DISSOLVED: isIso_of_mono_of_nonzero

theorem Simple.of_iso {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X :=
  { mono_isIso_iff_nonzero := fun f m => by
      constructor
      · intro h w
        have j : IsIso (f ≫ i.hom) := by infer_instance
        rw [Simple.mono_isIso_iff_nonzero] at j
        subst w
        simp at j
      · intro h
        have j : IsIso (f ≫ i.hom) := by
          apply isIso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← Category.comp_id f, ← i.hom_inv_id, ← Category.assoc]
        infer_instance }

theorem Simple.iff_of_iso {X Y : C} (i : X ≅ Y) : Simple X ↔ Simple Y :=
  ⟨fun _ => Simple.of_iso i.symm, fun _ => Simple.of_iso i⟩

-- DISSOLVED: kernel_zero_of_nonzero_from_simple

-- DISSOLVED: epi_of_nonzero_to_simple

theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f]
    (w : IsIso f → False) : f = 0 := by
  classical
    by_contra h
    exact w (isIso_of_mono_of_nonzero h)

-- DISSOLVED: id_nonzero

instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 _ (id_nonzero X)

section

theorem Simple.not_isZero (X : C) [Simple X] : ¬IsZero X := by
  simpa [Limits.IsZero.iff_id_eq_zero] using id_nonzero X

variable [HasZeroObject C]

open ZeroObject

variable (C)

theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_isIso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp ⟨⟨0, by aesop_cat⟩⟩ rfl

end

end

section Abelian

variable [Abelian C]

-- DISSOLVED: simple_of_cosimple

-- DISSOLVED: isIso_of_epi_of_nonzero

-- DISSOLVED: cokernel_zero_of_nonzero_to_simple

theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f]
    (w : IsIso f → False) : f = 0 := by
  classical
    by_contra h
    exact w (isIso_of_epi_of_nonzero h)

end Abelian

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

theorem Biprod.isIso_inl_iff_isZero (X Y : C) : IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y := by
  rw [biprod.isIso_inl_iff_id_eq_fst_comp_inl, ← biprod.total, add_right_eq_self]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [← IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
  · intro h
    rw [IsZero.iff_isSplitEpi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h, zero_comp]

theorem indecomposable_of_simple (X : C) [Simple X] : Indecomposable X :=
  ⟨Simple.not_isZero X, fun Y Z i => by
    refine or_iff_not_imp_left.mpr fun h => ?_
    rw [IsZero.iff_isSplitMono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl ≠ 0 at h
    have : Simple (Y ⊞ Z) := Simple.of_iso i.symm -- Porting note: this instance is needed
    rw [← Simple.mono_isIso_iff_nonzero biprod.inl] at h
    rwa [Biprod.isIso_inl_iff_isZero] at h⟩

end Indecomposable

section Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

open Subobject

instance {X : C} [Simple X] : Nontrivial (Subobject X) :=
  nontrivial_of_not_isZero (Simple.not_isZero X)

instance {X : C} [Simple X] : IsSimpleOrder (Subobject X) where
  eq_bot_or_eq_top := by
    rintro ⟨⟨⟨Y : C, ⟨⟨⟩⟩, f : Y ⟶ X⟩, m : Mono f⟩⟩
    change mk f = ⊥ ∨ mk f = ⊤
    by_cases h : f = 0
    · exact Or.inl (mk_eq_bot_iff_zero.mpr h)
    · refine Or.inr ((isIso_iff_mk_eq_top _).mp ((Simple.mono_isIso_iff_nonzero f).mpr h))

theorem simple_of_isSimpleOrder_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X := by
  constructor; intros Y f hf; constructor
  · intro i
    rw [Subobject.isIso_iff_mk_eq_top] at i
    intro w
    rw [← Subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (Subobject.mk f) with (h | h)
    · rw [Subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
    · exact (Subobject.isIso_iff_mk_eq_top _).mpr h

theorem simple_iff_subobject_isSimpleOrder (X : C) : Simple X ↔ IsSimpleOrder (Subobject X) :=
  ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_isSimpleOrder_subobject X⟩

theorem subobject_simple_iff_isAtom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y :=
  (simple_iff_subobject_isSimpleOrder _).trans
    ((OrderIso.isSimpleOrder_iff (subobjectOrderIso Y)).trans Set.isSimpleOrder_Iic_iff_isAtom)

end Subobject

end CategoryTheory
