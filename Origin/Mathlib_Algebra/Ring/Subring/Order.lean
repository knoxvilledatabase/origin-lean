/-
Extracted from Algebra/Ring/Subring/Order.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Subrings of ordered rings

We study subrings of ordered rings and prove their basic properties.

## Main definitions and results

* `Subring.orderedSubtype`: the inclusion `S → R` of a subring as an ordered ring homomorphism
* various ordered instances: a subring of an `IsOrderedRing` or an `IsStrictOrderRing` is again
  the respective kind of ordered ring.
-/

namespace Subring

variable {R S : Type*} [Ring R] [PartialOrder R] [SetLike S R] [SubringClass S R]

-- INSTANCE (free from Core): toIsOrderedRing

-- INSTANCE (free from Core): toIsStrictOrderedRing

def orderedSubtype (s : Subring R) : s →+*o R where
  __ := s.subtype
  monotone' := fun _ _ h ↦ h

end Subring
