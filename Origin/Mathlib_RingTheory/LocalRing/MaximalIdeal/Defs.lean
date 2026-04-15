/-
Extracted from RingTheory/LocalRing/MaximalIdeal/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Maximal ideal of local rings

We define the maximal ideal of a local ring as the ideal of all nonunits.

## Main definitions

* `IsLocalRing.maximalIdeal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of nonunits.

-/

namespace IsLocalRing

variable (R : Type*) [CommSemiring R] [IsLocalRing R]

def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right

end IsLocalRing
