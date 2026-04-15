/-
Extracted from Algebra/Order/Ring/Cone.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone`
that encodes axioms of `OrderedRing` and `LinearOrderedRing`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R] : Prop
    extends AddGroupConeClass S R, SubsemiringClass S R

structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

add_decl_doc RingCone.toAddGroupCone

-- INSTANCE (free from Core): RingCone.instSetLike

-- INSTANCE (free from Core): (R

-- INSTANCE (free from Core): RingCone.instRingConeClass
