/-
Extracted from Algebra/Order/ZeroLEOne.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Order.Basic

/-!
# Typeclass expressing `0 ≤ 1`.
-/

variable {α : Type*}

open Function

class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  /-- Zero is less than or equal to one. -/
  zero_le_one : (0 : α) ≤ 1

@[simp] lemma zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one

lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one

section

variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (NeZero.ne' 1)

variable (α)

lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one

end

alias one_pos := zero_lt_one
