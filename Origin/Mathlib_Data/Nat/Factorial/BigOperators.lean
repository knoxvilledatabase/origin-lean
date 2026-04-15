/-
Extracted from Data/Nat/Factorial/BigOperators.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Factorial with big operators

This file contains some lemmas on factorials in combination with big operators.

While in terms of semantics they could be in the `Basic.lean` file, importing
`Algebra.BigOperators.Group.Finset` leads to a cyclic import.

-/

open Finset Nat

namespace Nat

lemma monotone_factorial : Monotone factorial := fun _ _ => factorial_le

variable {α : Type*} (s : Finset α) (f : α → ℕ)

theorem prod_factorial_pos : 0 < ∏ i ∈ s, (f i)! := prod_pos fun _ _ ↦ factorial_pos _

theorem prod_factorial_dvd_factorial_sum : (∏ i ∈ s, (f i)!) ∣ (∑ i ∈ s, f i)! := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons, Finset.sum_cons]
    exact (mul_dvd_mul_left _ ih).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_eq_prod_range_add_one : ∀ n, (n)! = ∏ i ∈ range n, (i + 1)
  | 0 => rfl
  | n + 1 => by rw [factorial, prod_range_succ_comm, factorial_eq_prod_range_add_one n]
