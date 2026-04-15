/-
Extracted from Data/Multiset/ZeroCons.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Definition of `0` and `::ₘ`

This file defines constructors for multisets:

* `Zero (Multiset α)` instance: the empty multiset
* `Multiset.cons`: add one element to a multiset
* `Singleton α (Multiset α)` instance: multiset with one element

It also defines the following predicates on multisets:

* `Multiset.Rel`: `Rel r s t` lifts the relation `r` between two elements to a relation between `s`
  and `t`, s.t. there is a one-to-one mapping between elements in `s` and `t` following `r`.

## Notation

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.

## Main results

* `Multiset.rec`: recursion on adding one element to a multiset at a time.
-/

assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Empty multiset -/

protected def zero : Multiset α :=
  @nil α

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): inhabitedMultiset

-- INSTANCE (free from Core): [IsEmpty
