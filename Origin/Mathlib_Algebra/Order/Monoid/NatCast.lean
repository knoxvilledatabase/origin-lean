/-
Extracted from Algebra/Order/Monoid/NatCast.lean
Genuine: 5 of 7 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Order of numerals in an `AddMonoidWithOne`.
-/

variable {α : Type*}

open Function

-- DISSOLVED: lt_add_one

-- DISSOLVED: lt_one_add

variable [AddMonoidWithOne α]

lemma zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 2 := by
  rw [← one_add_one_eq_two]
  exact add_nonneg zero_le_one zero_le_one

lemma zero_le_three [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 3 := by
  rw [← two_add_one_eq_three]
  exact add_nonneg zero_le_two zero_le_one

lemma zero_le_four [Preorder α] [ZeroLEOneClass α] [AddLeftMono α] :
    (0 : α) ≤ 4 := by
  rw [← three_add_one_eq_four]
  exact add_nonneg zero_le_three zero_le_one

lemma one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] :
    (1 : α) ≤ 2 :=
  calc (1 : α) = 1 + 0 := (add_zero 1).symm
     _ ≤ 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

lemma one_le_two' [LE α] [ZeroLEOneClass α] [AddRightMono α] :
    (1 : α) ≤ 2 :=
  calc (1 : α) = 0 + 1 := (zero_add 1).symm
     _ ≤ 1 + 1 := by gcongr; exact zero_le_one
     _ = 2 := one_add_one_eq_two

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

variable [AddLeftMono α]
