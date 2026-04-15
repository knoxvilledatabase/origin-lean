/-
Extracted from Data/Nat/ChineseRemainder.lean
Genuine: 4 of 11 | Dissolved: 6 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Chinese Remainder Theorem

This file provides definitions and theorems for the Chinese Remainder Theorem. These are used in
Gödel's Beta function, which is used in proving Gödel's incompleteness theorems.

## Main result

- `chineseRemainderOfList`: Definition of the Chinese remainder of a list

## Tags

Chinese Remainder Theorem, Gödel, beta function
-/

namespace Nat

variable {ι : Type*}

lemma modEq_list_prod_iff {a b} {l : List ℕ} (co : l.Pairwise Coprime) :
    a ≡ b [MOD l.prod] ↔ ∀ i, a ≡ b [MOD l.get i] := by
  induction' l with m l ih
  · simp [modEq_one]
  · have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp only [List.prod_cons, ← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co),
      List.length_cons]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp_all
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

lemma modEq_list_prod_iff' {a b} {s : ι → ℕ} {l : List ι} (co : l.Pairwise (Coprime on s)) :
    a ≡ b [MOD (l.map s).prod] ↔ ∀ i ∈ l, a ≡ b [MOD s i] := by
  induction' l with i l ih
  · simp [modEq_one]
  · have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

variable (a s : ι → ℕ)

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
    exact ((modEq_list_prod_iff' co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)

@[simp] theorem chineseRemainderOfList_nil :
    (chineseRemainderOfList a s [] List.Pairwise.nil : ℕ) = 0 := rfl

-- DISSOLVED: chineseRemainderOfList_lt_prod

theorem chineseRemainderOfList_modEq_unique (l : List ι)
    (co : l.Pairwise (Coprime on s)) {z} (hz : ∀ i ∈ l, z ≡ a i [MOD s i]) :
    z ≡ chineseRemainderOfList a s l co [MOD (l.map s).prod] := by
  induction' l with i l ih
  · simp [modEq_one]
  · simp only [List.map_cons, List.prod_cons, chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := by
      simp only [coprime_list_prod_right_iff, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro j hj
      exact (List.pairwise_cons.mp co).1 j hj
    exact chineseRemainder_modEq_unique this
      (hz i (List.mem_cons_self _ _)) (ih co.of_cons (fun j hj => hz j (List.mem_cons_of_mem _ hj)))

-- DISSOLVED: chineseRemainderOfList_perm

-- DISSOLVED: chineseRemainderOfMultiset

-- DISSOLVED: chineseRemainderOfMultiset_lt_prod

-- DISSOLVED: chineseRemainderOfFinset

-- DISSOLVED: chineseRemainderOfFinset_lt_prod

end Nat
