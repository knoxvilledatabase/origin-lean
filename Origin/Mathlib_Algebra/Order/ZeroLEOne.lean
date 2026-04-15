/-
Extracted from Algebra/Order/ZeroLEOne.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclass expressing `0 ≤ 1`.
-/

variable {α : Type*}

open Function

class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  /-- Zero is less than or equal to one. -/
  zero_le_one : (0 : α) ≤ 1
