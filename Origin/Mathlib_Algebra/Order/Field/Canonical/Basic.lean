/-
Extracted from Algebra/Order/Field/Canonical/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Field.Canonical.Defs

/-!
# Lemmas about canonically ordered semifields.

-/

variable {α : Type*}

section CanonicallyLinearOrderedSemifield

variable [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]

end CanonicallyLinearOrderedSemifield
