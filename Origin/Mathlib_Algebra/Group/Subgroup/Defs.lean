/-
Extracted from Algebra/Group/Subgroup/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subgroups

This file defines multiplicative and additive subgroups as an extension of submonoids, in a bundled
form.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup G` : the type of subgroups of a group `G`

* `AddSubgroup A` : the type of subgroups of an additive group `A`

* `Subgroup.subtype` : the natural group homomorphism from a subgroup of group `G` to `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

assert_not_exists RelIso IsOrderedMonoid Multiset MonoidWithZero

open Function

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

section SubgroupClass

class InvMemClass (S : Type*) (G : outParam Type*) [Inv G] [SetLike S G] : Prop where
  /-- `s` is closed under inverses -/
  inv_mem : ∀ {s : S} {x}, x ∈ s → x⁻¹ ∈ s

export InvMemClass (inv_mem)

class NegMemClass (S : Type*) (G : outParam Type*) [Neg G] [SetLike S G] : Prop where
  /-- `s` is closed under negation -/
  neg_mem : ∀ {s : S} {x}, x ∈ s → -x ∈ s

export NegMemClass (neg_mem)

class HasMemOrNegMem {S G : Type*} [Neg G] [SetLike S G] (s : S) : Prop where
  mem_or_neg_mem (s) (a : G) : a ∈ s ∨ -a ∈ s
