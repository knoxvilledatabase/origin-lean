/-
Extracted from Data/Int/Order/Units.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about units in `ℤ`, which interact with the order structure.
-/

namespace Int

theorem isUnit_iff_abs_eq {x : ℤ} : IsUnit x ↔ abs x = 1 := by
  rw [isUnit_iff_natAbs_eq, abs_eq_natAbs, ← Int.ofNat_one, natCast_inj]

theorem isUnit_sq {a : ℤ} (ha : IsUnit a) : a ^ 2 = 1 := by rw [sq, isUnit_mul_self ha]
