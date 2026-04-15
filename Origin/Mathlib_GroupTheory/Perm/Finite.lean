/-
Extracted from GroupTheory/Perm/Finite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Permutations on `Fintype`s

This file contains miscellaneous lemmas about `Equiv.Perm` and `Equiv.swap`, building on top
of those in `Mathlib/Logic/Equiv/Basic.lean` and other files in `Mathlib/GroupTheory/Perm/*`.
-/

universe u v

open Equiv Function Fintype Finset

variable {α : Type u} {β : Type v}

namespace Equiv.Perm

section Conjugation

variable [DecidableEq α] [Fintype α] {σ τ : Perm α}

theorem isConj_of_support_equiv
    (f : { x // x ∈ (σ.support : Set α) } ≃ { x // x ∈ (τ.support : Set α) })
    (hf : ∀ (x : α) (hx : x ∈ (σ.support : Set α)),
      (f ⟨σ x, apply_mem_support.2 hx⟩ : α) = τ ↑(f ⟨x, hx⟩)) :
    IsConj σ τ := by
  refine isConj_iff.2 ⟨Equiv.extendSubtype f, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x ∈ σ.support
  · rw [Equiv.extendSubtype_apply_of_mem, Equiv.extendSubtype_apply_of_mem]
    · exact hf x (Finset.mem_coe.2 hx)
  · rwa [Classical.not_not.1 ((not_congr mem_support).1 (Equiv.extendSubtype_not_mem f _ _)),
      Classical.not_not.1 ((not_congr mem_support).mp hx)]

end Conjugation

theorem perm_symm_on_of_perm_on_finset {s : Finset α} {f : Perm α} (h : ∀ x ∈ s, f x ∈ s) {y : α}
    (hy : y ∈ s) : f.symm y ∈ s := by
  have h0 : ∀ y ∈ s, ∃ (x : _) (hx : x ∈ s), y = (fun i (_ : i ∈ s) => f i) x hx :=
    Finset.surj_on_of_inj_on_of_card_le (fun x hx => (fun i _ => f i) x hx) (fun a ha => h a ha)
      (fun a₁ a₂ ha₁ ha₂ heq => (Equiv.apply_eq_iff_eq f).mp heq) rfl.ge
  obtain ⟨y2, hy2, rfl⟩ := h0 y hy
  simpa using hy2
