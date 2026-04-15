/-
Extracted from Combinatorics/SetFamily/Intersecting.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Intersecting families

This file defines intersecting families and proves their basic properties.

## Main declarations

* `Set.Intersecting`: Predicate for a set of elements in a generalized Boolean algebra to be an
  intersecting family.
* `Set.Intersecting.card_le`: An intersecting family can only take up to half the elements, because
  `a` and `aᶜ` cannot simultaneously be in it.
* `Set.Intersecting.is_max_iff_card_eq`: Any maximal intersecting family takes up half the elements.
* `Set.IsIntersectingOf`: Predicate stating that a family `𝒜` of finsets is `L`-intersecting, i.e.,
  meaning the intersection size of every pair of distinct members of `𝒜` belongs to `L ⊆ ℕ`.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

assert_not_exists Monoid

open Finset

namespace Set

section SemilatticeInf

variable {α : Type*}

variable [SemilatticeInf α] [OrderBot α] {s t : Set α} {a b c : α}

def Intersecting (s : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬Disjoint a b
