/-
Extracted from Algebra/Order/Field/Power.lean
Genuine: 7 of 10 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about powers in ordered fields.
-/

variable {α : Type*}

open Function Int

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

protected theorem Even.zpow_nonneg (hn : Even n) (a : α) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := even_two.zpow_nonneg _

lemma zpow_neg_two_nonneg (a : α) : 0 ≤ a ^ (-2 : ℤ) := even_neg_two.zpow_nonneg _

-- DISSOLVED: Even.zpow_pos

-- DISSOLVED: zpow_two_pos_of_ne_zero

-- DISSOLVED: Even.zpow_pos_iff

theorem Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

protected lemma Odd.zpow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

theorem Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.zpow_neg_iff, zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero

lemma Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff
