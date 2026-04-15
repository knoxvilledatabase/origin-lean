/-
Extracted from Algebra/Order/Field/Canonical.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Canonically ordered semifields
-/

variable {α : Type*} [Semifield α] [LinearOrder α] [CanonicallyOrderedAdd α]

-- DISSOLVED: CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

variable [IsStrictOrderedRing α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
