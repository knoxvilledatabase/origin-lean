/-
Extracted from Data/Int/Order/Units.lean
Genuine: 8 of 11 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Lemmas about units in `ℤ`, which interact with the order structure.
-/

namespace Int

theorem isUnit_iff_abs_eq {x : ℤ} : IsUnit x ↔ abs x = 1 := by
  rw [isUnit_iff_natAbs_eq, abs_eq_natAbs, ← Int.ofNat_one, natCast_inj]

theorem isUnit_sq {a : ℤ} (ha : IsUnit a) : a ^ 2 = 1 := by rw [sq, isUnit_mul_self ha]

@[simp]
theorem units_sq (u : ℤˣ) : u ^ 2 = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, isUnit_sq u.isUnit]

alias units_pow_two := units_sq

@[simp]
theorem units_mul_self (u : ℤˣ) : u * u = 1 := by rw [← sq, units_sq]

@[simp]
theorem units_inv_eq_self (u : ℤˣ) : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, units_mul_self]

theorem units_div_eq_mul (u₁ u₂ : ℤˣ) : u₁ / u₂ = u₁ * u₂ := by
  rw [div_eq_mul_inv, units_inv_eq_self]

@[simp]
theorem units_coe_mul_self (u : ℤˣ) : (u * u : ℤ) = 1 := by
  rw [← Units.val_mul, units_mul_self, Units.val_one]

-- DISSOLVED: neg_one_pow_ne_zero

-- DISSOLVED: sq_eq_one_of_sq_lt_four

-- DISSOLVED: sq_eq_one_of_sq_le_three

theorem units_pow_eq_pow_mod_two (u : ℤˣ) (n : ℕ) : u ^ n = u ^ (n % 2) := by
  conv =>
    lhs
    rw [← Nat.mod_add_div n 2]
    rw [pow_add, pow_mul, units_sq, one_pow, mul_one]

end Int
