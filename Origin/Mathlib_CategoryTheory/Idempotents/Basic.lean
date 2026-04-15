/-
Extracted from CategoryTheory/Idempotents/Basic.lean
Genuine: 8 of 12 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `IsIdempotentComplete C` expresses that `C` is idempotent complete, i.e.
  all idempotents in `C` split. Other characterisations of idempotent completeness are given
  by `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` and
  `isIdempotentComplete_iff_idempotents_have_kernels`.
- `isIdempotentComplete_of_abelian` expresses that abelian categories are
  idempotent complete.
- `isIdempotentComplete_iff_ofEquivalence` expresses that if two categories `C` and `D`
  are equivalent, then `C` is idempotent complete iff `D` is.
- `isIdempotentComplete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
  iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open Opposite

namespace CategoryTheory

variable (C : Type*) [Category* C]

class IsIdempotentComplete : Prop where
  /-- A category is idempotent complete iff all idempotent endomorphisms `p`
  split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
  idempotents_split :
    ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

namespace Idempotents

set_option backward.isDefEq.respectTransparency false in

variable {C} in

theorem idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) :
    (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p := by
  simp only [comp_sub, sub_comp, id_comp, comp_id, hp, sub_self, sub_zero]

-- INSTANCE (free from Core): (priority

variable {C}

theorem split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p')
    (h : ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
    ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  grind

theorem split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X')
    (hpp' : p ≫ φ.hom = φ.hom ≫ p') :
    (∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
      ∃ (Y' : C) (i' : Y' ⟶ X') (e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p, ← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    simp

set_option backward.isDefEq.respectTransparency false in

theorem Equivalence.isIdempotentComplete {D : Type*} [Category* D] (ε : C ≌ D)
    (h : IsIdempotentComplete C) : IsIdempotentComplete D := by
  refine ⟨?_⟩
  intro X' p hp
  let φ := ε.counitIso.symm.app X'
  erw [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases IsIdempotentComplete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
      (by rw [← ε.inverse.map_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use ε.functor.obj Y, ε.functor.map i, ε.functor.map e
  constructor
  · rw [← ε.functor.map_comp, h₁, ε.functor.map_id]
  · simp only [← ε.functor.map_comp, h₂, Equivalence.fun_inv_map]
    rfl

theorem isIdempotentComplete_iff_of_equivalence {D : Type*} [Category* D] (ε : C ≌ D) :
    IsIdempotentComplete C ↔ IsIdempotentComplete D := by
  constructor
  · exact Equivalence.isIdempotentComplete ε
  · exact Equivalence.isIdempotentComplete ε.symm

theorem isIdempotentComplete_of_isIdempotentComplete_opposite (h : IsIdempotentComplete Cᵒᵖ) :
    IsIdempotentComplete C := by
  refine ⟨?_⟩
  intro X p hp
  rcases IsIdempotentComplete.idempotents_split (op X) p.op (by rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simp only [← unop_comp, h₁]
    rfl
  · simp only [← unop_comp, h₂]
    rfl

theorem isIdempotentComplete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C := by
  constructor
  · exact isIdempotentComplete_of_isIdempotentComplete_opposite
  · intro h
    apply isIdempotentComplete_of_isIdempotentComplete_opposite
    rw [isIdempotentComplete_iff_of_equivalence (opOpEquivalence C)]
    exact h

-- INSTANCE (free from Core): [IsIdempotentComplete

end Idempotents

end CategoryTheory
