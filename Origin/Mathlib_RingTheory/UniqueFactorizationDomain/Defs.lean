/-
Extracted from RingTheory/UniqueFactorizationDomain/Defs.lean
Genuine: 1 of 3 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Unique factorization

## Main Definitions
* `WfDvdMonoid` holds for `Monoid`s for which a strict divisibility relation is
  well-founded.
* `UniqueFactorizationMonoid` holds for `WfDvdMonoid`s where
  `Irreducible` is equivalent to `Prime`
-/

assert_not_exists Field Finsupp Ideal

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

variable [WfDvdMonoid α]

-- DISSOLVED: exists_irreducible_factor
