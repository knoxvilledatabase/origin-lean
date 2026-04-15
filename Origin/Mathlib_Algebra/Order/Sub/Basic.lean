/-
Extracted from Algebra/Order/Sub/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

variable {α : Type*}

section CanonicallyOrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {a b c : α}

theorem add_tsub_cancel_iff_le : a + (b - a) = b ↔ a ≤ b :=
  ⟨fun h => le_iff_exists_add.mpr ⟨b - a, h.symm⟩, add_tsub_cancel_of_le⟩

theorem tsub_add_cancel_iff_le : b - a + a = b ↔ a ≤ b := by
  rw [add_comm]
  exact add_tsub_cancel_iff_le

theorem tsub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, tsub_le_iff_left, add_zero]

alias ⟨_, tsub_eq_zero_of_le⟩ := tsub_eq_zero_iff_le
