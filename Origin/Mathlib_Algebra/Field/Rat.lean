/-
Extracted from Algebra/Field/Rat.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The rational numbers form a field

This file contains the field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

namespace Rat

-- INSTANCE (free from Core): instField

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

-- INSTANCE (free from Core): instDivisionRing

protected lemma inv_nonneg {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)

protected lemma div_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg ha (Rat.inv_nonneg hb)

end Rat

namespace NNRat

-- INSTANCE (free from Core): instInv

-- INSTANCE (free from Core): instDiv

-- INSTANCE (free from Core): instZPow
