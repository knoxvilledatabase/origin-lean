/-
Extracted from Algebra/Group/Submonoid/Defs.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Submonoids: definition

This file defines bundled multiplicative and additive submonoids. We also define
a `CompleteLattice` structure on `Submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `Submonoid.dense_induction` and
`MonoidHom.ofClosureEqTopLeft`/`MonoidHom.ofClosureEqTopRight`.

## Main definitions

* `Submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : Set M)`.
* `AddSubmonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `Submonoid` namespace, there is a corresponding
definition in the `AddSubmonoid` namespace.

* `Submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `Submonoid`.
* `MonoidHom.eqLocusM`: the submonoid of elements `x : M` such that `f x = g x`;

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `Submonoid M` does not actually require `Monoid M`, instead requiring only the weaker
`MulOneClass M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `Submonoid` is implemented by extending `Subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/

assert_not_exists RelIso CompleteLattice MonoidWithZero

variable {M : Type*} {N : Type*}

section NonAssoc

variable [MulOneClass M] {s : Set M}

class OneMemClass (S : Type*) (M : outParam Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (1 : M) ∈ s

export OneMemClass (one_mem)

class ZeroMemClass (S : Type*) (M : outParam Type*) [Zero M] [SetLike S M] : Prop where
  /-- By definition, if we have `ZeroMemClass S M`, we have `0 ∈ s` for all `s : S`. -/
  zero_mem : ∀ s : S, (0 : M) ∈ s

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

attribute [simp, aesop safe (rule_sets := [SetLike])] one_mem zero_mem

structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (1 : M) ∈ carrier

end

add_decl_doc Submonoid.toSubsemigroup

class SubmonoidClass (S : Type*) (M : outParam Type*) [MulOneClass M] [SetLike S M] : Prop
    extends MulMemClass S M, OneMemClass S M

structure AddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubsemigroup M where
  /-- An additive submonoid contains `0`. -/
  zero_mem' : (0 : M) ∈ carrier

end

add_decl_doc AddSubmonoid.toAddSubsemigroup

class AddSubmonoidClass (S : Type*) (M : outParam Type*) [AddZeroClass M] [SetLike S M] : Prop
  extends AddMemClass S M, ZeroMemClass S M

attribute [to_additive] Submonoid SubmonoidClass
