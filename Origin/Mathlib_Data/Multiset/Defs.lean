/-
Extracted from Data/Multiset/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multisets

Multisets are finite sets with duplicates allowed. They are implemented here as the quotient of
lists by permutation. This gives them computational content.

This file contains the definition of `Multiset` and the basic predicates. Most operations
have been split off into their own files. The goal is that we can define `Finset` with only
importing `Multiset.Defs`.

## Main definitions

* `Multiset`: the type of finite sets with duplicates allowed.

* `Coe (List α) (Multiset α)`: turn a list into a multiset by forgetting the order.
* `Multiset.pmap`: map a partial function defined on a superset of the multiset's elements.
* `Multiset.attach`: add a proof of membership to the elements of the multiset.
* `Multiset.card`: number of elements of a multiset (counted with repetition).

* `Membership α (Multiset α)` instance: `x ∈ s` if `x` has multiplicity at least one in `s`.
* `Subset (Multiset α)` instance: `s ⊆ t` if every `x ∈ s` also enjoys `x ∈ t`.
* `PartialOrder (Multiset α)` instance: `s ≤ t` if all `x` have multiplicity in
  `s` less than their multiplicity in `t`.
* `Multiset.Pairwise`: `Pairwise r s` holds iff there exists a list of elements
  of `s` such that `r` holds pairwise.
* `Multiset.Nodup`: `Nodup s` holds if the multiplicity of any element is at most 1.

## Notation (defined later)

* `0`: The empty multiset.
* `{a}`: The multiset containing a single occurrence of `a`.
* `a ::ₘ s`: The multiset containing one more occurrence of `a` than `s` does.
* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.
* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

assert_not_exists Monoid OrderHom

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

def Multiset.{u} (α : Type u) : Type u :=
  Quotient (List.isSetoid α)

namespace Multiset
