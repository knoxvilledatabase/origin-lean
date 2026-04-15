/-
Extracted from RingTheory/LocalRing/MaximalIdeal/Defs.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.LocalRing.Basic

/-!

# Maximal ideal of local rings

We define the maximal ideal of a local ring as the ideal of all non units.

## Main definitions

* `IsLocalRing.maximalIdeal`: The unique maximal ideal for a local rings. Its carrier set is the
  set of non units.

-/

namespace IsLocalRing

variable (R : Type*) [CommSemiring R] [IsLocalRing R]

def maximalIdeal : Ideal R where
  carrier := nonunits R
  zero_mem' := zero_mem_nonunits.2 <| zero_ne_one
  add_mem' {_ _} hx hy := nonunits_add hx hy
  smul_mem' _ _ := mul_mem_nonunits_right

end IsLocalRing
