/-
Extracted from Algebra/Divisibility/Units.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Divisibility and units

## Main definition

* `IsRelPrime x y`: that `x` and `y` are relatively prime, defined to mean that the only common
  divisors of `x` and `y` are the units.

-/

variable {α : Type*}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩

theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ ↦ ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ ↦ eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right

theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α}
