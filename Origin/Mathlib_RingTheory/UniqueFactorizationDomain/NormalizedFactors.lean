/-
Extracted from RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unique factorization and normalization

## Main definitions
* `UniqueFactorizationMonoid.normalizedFactors`: choose a multiset of prime factors that are unique
  by normalizing them.
* `UniqueFactorizationMonoid.normalizationMonoid`: choose a way of normalizing the elements of a UFM
-/

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [NormalizationMonoid α]

variable [UniqueFactorizationMonoid α]

noncomputable def normalizedFactors (a : α) : Multiset α :=
  Multiset.map normalize <| factors a
