/-
Extracted from Data/ZMod/Coprime.lean
Genuine: 1 of 4 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `ZMod p` vanishes if and only if
`a` and `p` are not coprime.
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

set_option backward.isDefEq.respectTransparency false in

theorem coe_int_isUnit_iff_isCoprime (n : ℤ) (m : ℕ) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : ℤ) n := by
  rw [Int.isCoprime_iff_nat_coprime, Nat.coprime_comm, ← isUnit_iff_coprime, Associated.isUnit_iff]
  simpa only [eq_intCast, Int.cast_natCast] using (Int.associated_natAbs _).map (Int.castRingHom _)

-- DISSOLVED: eq_zero_iff_gcd_ne_one

-- DISSOLVED: ne_zero_of_gcd_eq_one

-- DISSOLVED: eq_zero_of_gcd_ne_one

end ZMod
