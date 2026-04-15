/-
Extracted from Algebra/Order/Monoid/Unbundled/Units.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas for units in an ordered monoid
-/

variable {M : Type*} [Monoid M] [LE M]

namespace Units

section MulLeftMono

variable [MulLeftMono M] (u : Mˣ) {a b : M}

theorem mulLECancellable_val : MulLECancellable (↑u : M) := fun _ _ h ↦ by
  simpa using mul_le_mul_right h ↑u⁻¹

private theorem mul_le_mul_iff_left : u * a ≤ u * b ↔ a ≤ b :=
  u.mulLECancellable_val.mul_le_mul_iff_left

theorem inv_mul_le_iff : u⁻¹ * a ≤ b ↔ a ≤ u * b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]

theorem le_inv_mul_iff : a ≤ u⁻¹ * b ↔ u * a ≤ b := by
  rw [← u.mul_le_mul_iff_left, mul_inv_cancel_left]
