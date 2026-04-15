/-
Extracted from Data/Nat/Cast/Order/Field.lean
Genuine: 7 of 9 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Field.Basic

/-!
# Cast of naturals into ordered fields

This file concerns the canonical homomorphism `ℕ → F`, where `F` is a `LinearOrderedSemifield`.

## Main results

 * `Nat.cast_div_le`: in all cases, `↑(m / n) ≤ ↑m / ↑ n`
-/

namespace Nat

variable {α : Type*} [LinearOrderedSemifield α]

lemma cast_inv_le_one : ∀ n : ℕ, (n⁻¹ : α) ≤ 1
  | 0 => by simp
  | n + 1 => inv_le_one_of_one_le₀ <| by simp [Nat.cast_nonneg]

theorem cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n := by
  cases n
  · rw [cast_zero, div_zero, Nat.div_zero, cast_zero]
  rw [le_div_iff₀, ← Nat.cast_mul, @Nat.cast_le]
  · exact Nat.div_mul_le_self m _
  · exact Nat.cast_pos.2 (Nat.succ_pos _)

theorem inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
  inv_pos.2 <| add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

theorem one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) := by
  rw [one_div]
  exact inv_pos_of_nat

theorem one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) := by
  refine one_div_le_one_div_of_le ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

theorem one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) := by
  refine one_div_lt_one_div_of_lt ?_ ?_
  · exact Nat.cast_add_one_pos _
  · simpa

-- DISSOLVED: one_div_cast_pos

theorem one_div_cast_nonneg (n : ℕ) : 0 ≤ 1 / (n : α) := one_div_nonneg.mpr (cast_nonneg' n)

-- DISSOLVED: one_div_cast_ne_zero

end Nat
