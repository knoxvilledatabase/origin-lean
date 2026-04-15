/-
Extracted from Data/Nat/ChineseRemainder.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chinese Remainder Theorem

This file provides definitions and theorems for the Chinese Remainder Theorem. These are used in
Gödel's Beta function, which is used in proving Gödel's incompleteness theorems.

## Main result

- `chineseRemainderOfList`: Definition of the Chinese remainder of a list

## Tags

Chinese Remainder Theorem, Gödel, beta function
-/

open scoped Function -- required for scoped `on` notation

namespace Nat

variable {ι : Type*}

lemma modEq_list_prod_iff {a b} {l : List ℕ} (co : l.Pairwise Coprime) :
    a ≡ b [MOD l.prod] ↔ ∀ i, a ≡ b [MOD l.get i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons m l ih =>
    have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

lemma modEq_list_map_prod_iff {a b} {s : ι → ℕ} {l : List ι} (co : l.Pairwise (Coprime on s)) :
    a ≡ b [MOD (l.map s).prod] ↔ ∀ i ∈ l, a ≡ b [MOD s i] := by
  induction l with
  | nil => simp [modEq_one]
  | cons i l ih =>
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

variable (a s : ι → ℕ)

set_option linter.style.whitespace false in -- manual alignment is not recognised

def chineseRemainderOfList : (l : List ι) → l.Pairwise (Coprime on s) →
    { k // ∀ i ∈ l, k ≡ a i [MOD s i] }
  | [],     _  => ⟨0, by simp⟩
  | i :: l, co => by
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    use k
    simp only [List.mem_cons, forall_eq_or_imp, k.prop.1, true_and]
    intro j hj
    exact ((modEq_list_map_prod_iff co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)
