/-
Extracted from RingTheory/TwoSidedIdeal/Basic.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Two Sided Ideals

In this file, for any `Ring R`, we reinterpret `I : RingCon R` as a two-sided-ideal of a ring.

## Main definitions and results

* `TwoSidedIdeal`: For any `NonUnitalNonAssocRing R`, `TwoSidedIdeal R` is a wrapper around
  `RingCon R`.
* `TwoSidedIdeal.setLike`: Every `I : TwoSidedIdeal R` can be interpreted as a set of `R` where
  `x ∈ I` if and only if `I.ringCon x 0`.
* `TwoSidedIdeal.addCommGroup`: Every `I : TwoSidedIdeal R` is an abelian group.

-/

assert_not_exists LinearMap

open MulOpposite

section definitions

structure TwoSidedIdeal (R : Type*) [NonUnitalNonAssocRing R] where
  /-- every two-sided-ideal is induced by a congruence relation on the ring. -/
  ringCon : RingCon R

end definitions

namespace TwoSidedIdeal

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

-- INSTANCE (free from Core): [Nontrivial

-- INSTANCE (free from Core): setLike

-- INSTANCE (free from Core): :
