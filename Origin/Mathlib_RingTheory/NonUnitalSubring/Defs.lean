/-
Extracted from RingTheory/NonUnitalSubring/Defs.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# `NonUnitalSubring`s

Let `R` be a non-unital ring. This file defines the "bundled" non-unital subring type
`NonUnitalSubring R`, a type whose terms correspond to non-unital subrings of `R`.
This is the preferred way to talk about non-unital subrings in mathlib.

## Main definitions

Notation used here:

`(R : Type u) [NonUnitalRing R] (S : Type u) [NonUnitalRing S] (f g : R →ₙ+* S)`
`(A : NonUnitalSubring R) (B : NonUnitalSubring S) (s : Set R)`

* `NonUnitalSubring R` : the type of non-unital subrings of a ring `R`.

## Implementation notes

A non-unital subring is implemented as a `NonUnitalSubsemiring` which is also an
additive subgroup.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a non-unital subring's underlying set.

## Tags
non-unital subring
-/

assert_not_exists RelIso

universe u v w

section Basic

variable {R : Type u} {S : Type v} [NonUnitalNonAssocRing R]

section NonUnitalSubringClass

class NonUnitalSubringClass (S : Type*) (R : Type u) [NonUnitalNonAssocRing R] [SetLike S R] : Prop
  extends NonUnitalSubsemiringClass S R, NegMemClass S R where

-- INSTANCE (free from Core): (priority

variable [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

namespace NonUnitalSubringClass

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

def subtype (s : S) : s →ₙ+* R :=
  { NonUnitalSubsemiringClass.subtype s,
    AddSubgroupClass.subtype s with
    toFun := Subtype.val }

variable {s} in
