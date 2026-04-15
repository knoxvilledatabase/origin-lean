/-
Extracted from Algebra/Star/NonUnitalSubalgebra.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Non-unital Star Subalgebras

In this file we define `NonUnitalStarSubalgebra`s and the usual operations on them
(`map`, `comap`).

## TODO

* once we have scalar actions by semigroups (as opposed to monoids), implement the action of a
  non-unital subalgebra on the larger algebra.
-/

open Module

namespace StarMemClass

-- INSTANCE (free from Core): instInvolutiveStar

-- INSTANCE (free from Core): instStarMul

-- INSTANCE (free from Core): instStarAddMonoid

-- INSTANCE (free from Core): instStarRing

-- INSTANCE (free from Core): instStarModule

end StarMemClass

universe u u' v v' w w' w''

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

namespace NonUnitalStarSubalgebraClass

variable [CommSemiring R] [NonUnitalNonAssocSemiring A]

variable [Star A] [Module R A]

variable {S : Type w''} [SetLike S A] [NonUnitalSubsemiringClass S A]

variable [hSR : SMulMemClass S R A] [StarMemClass S A] (s : S)

def subtype (s : S) : s →⋆ₙₐ[R] A :=
  { NonUnitalSubalgebraClass.subtype s with
    toFun := Subtype.val
    map_star' := fun _ => rfl }

variable {s} in
