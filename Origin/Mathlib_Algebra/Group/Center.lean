/-
Extracted from Algebra/Group/Center.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Set.addCenter`: the center of an additive magma
* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

## See also

See `Mathlib/GroupTheory/Subsemigroup/Center.lean` for the definition of the center as a
subsemigroup:
* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

See `Mathlib/GroupTheory/Subsemigroup/Centralizer.lean` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/

assert_not_exists HeytingAlgebra RelIso Finset MonoidWithZero Subsemigroup

variable {M : Type*} {S T : Set M}

structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : AddCommute z a
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)
