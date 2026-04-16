/-
Extracted from Algebra/Order/Ring/Cone.lean
Genuine: 5 | Conflates: 0 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Ring.Subsemiring.Order

noncomputable section

/-!
# Construct ordered rings from rings with a specified positive cone.

In this file we provide the structure `RingCone`
that encodes axioms of `OrderedRing` and `LinearOrderedRing`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in rings and the corresponding ordered rings.
-/

class RingConeClass (S : Type*) (R : outParam Type*) [Ring R] [SetLike S R]
    extends AddGroupConeClass S R, SubsemiringClass S R : Prop

structure RingCone (R : Type*) [Ring R] extends Subsemiring R, AddGroupCone R

instance RingCone.instSetLike (R : Type*) [Ring R] : SetLike (RingCone R) R where
  coe C := C.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance RingCone.instRingConeClass (R : Type*) [Ring R] :
    RingConeClass (RingCone R) R where
  add_mem {C} := C.add_mem'
  zero_mem {C} := C.zero_mem'
  mul_mem {C} := C.mul_mem'
  one_mem {C} := C.one_mem'
  eq_zero_of_mem_of_neg_mem {C} := C.eq_zero_of_mem_of_neg_mem'

namespace RingCone

variable {T : Type*} [OrderedRing T] {a : T}

variable (T) in

def nonneg : RingCone T where
  __ := Subsemiring.nonneg T
  eq_zero_of_mem_of_neg_mem' {a} := by simpa using ge_antisymm

instance nonneg.isMaxCone {T : Type*} [LinearOrderedRing T] : IsMaxCone (nonneg T) where
  mem_or_neg_mem := mem_or_neg_mem (C := AddGroupCone.nonneg T)

end RingCone

variable {S R : Type*} [Ring R] [SetLike S R] (C : S)

@[reducible] def OrderedRing.mkOfCone [RingConeClass S R] : OrderedRing R where
  __ := ‹Ring R›
  __ := OrderedAddCommGroup.mkOfCone C
  zero_le_one := show _ ∈ C by simpa using one_mem C
  mul_nonneg x y xnn ynn := show _ ∈ C by simpa using mul_mem xnn ynn

@[reducible] def LinearOrderedRing.mkOfCone
    [IsDomain R] [RingConeClass S R] [IsMaxCone C]
    (dec : DecidablePred (· ∈ C)) : LinearOrderedRing R where
  __ := OrderedRing.mkOfCone C
  __ := OrderedRing.toStrictOrderedRing R
  le_total a b := by simpa using mem_or_neg_mem (b - a)
  decidableLE _ _ := dec _
