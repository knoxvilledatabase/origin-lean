/-
Extracted from Algebra/Group/Subsemigroup/Defs.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subsemigroups: definition

This file defines bundled multiplicative and additive subsemigroups.

## Main definitions

* `Subsemigroup M`: the type of bundled subsemigroup of a magma `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubsemigroup M` : the type of bundled subsemigroups of an additive magma `M`.

For each of the following definitions in the `Subsemigroup` namespace, there is a corresponding
definition in the `AddSubsemigroup` namespace.

* `Subsemigroup.copy` : copy of a subsemigroup with `carrier` replaced by a set that is equal but
  possibly not definitionally equal to the carrier of the original `Subsemigroup`.

Similarly, for each of these definitions in the `MulHom` namespace, there is a corresponding
definition in the `AddHom` namespace.

* `MulHom.eqLocus f g`: the subsemigroup of those `x` such that `f x = g x`

## Implementation notes

Subsemigroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subsemigroup's underlying set.

Note that `Subsemigroup M` does not actually require `Semigroup M`,
instead requiring only the weaker `Mul M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers.

## Tags
subsemigroup, subsemigroups
-/

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [Mul M] {s : Set M}

class MulMemClass (S : Type*) (M : outParam Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s

export MulMemClass (mul_mem)

class AddMemClass (S : Type*) (M : outParam Type*) [Add M] [SetLike S M] : Prop where
  /-- A substructure satisfying `AddMemClass` is closed under addition. -/
  add_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a + b ∈ s

export AddMemClass (add_mem)

attribute [to_additive] MulMemClass

attribute [aesop 90% (rule_sets := [SetLike])] mul_mem add_mem

structure Subsemigroup (M : Type*) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

structure AddSubsemigroup (M : Type*) [Add M] where
  /-- The carrier of an additive subsemigroup. -/
  carrier : Set M
  /-- The sum of two elements of an additive subsemigroup belongs to the subsemigroup. -/
  add_mem' {a b} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier

attribute [to_additive AddSubsemigroup] Subsemigroup

namespace Subsemigroup
