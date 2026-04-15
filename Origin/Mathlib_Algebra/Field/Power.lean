/-
Extracted from Algebra/Field/Power.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Results about powers in fields or division rings.

This file exists to ensure we can define `Field` with minimal imports,
so it contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/

variable {α : Type*}

section DivisionRing

variable [DivisionRing α] {n : ℤ}

theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end DivisionRing
