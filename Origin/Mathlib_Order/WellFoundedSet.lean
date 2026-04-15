/-
Extracted from Order/WellFoundedSet.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Well-founded sets

This file introduces versions of `WellFounded` and `WellQuasiOrdered` for sets.

## Main Definitions

* `Set.WellFoundedOn s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
* `Set.IsWF s` indicates that `<` is well-founded when restricted to `s`.
* `Set.PartiallyWellOrderedOn s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
* `Set.IsPWO s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results

* Higman's Lemma, `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂`,
  shows that if `r` is partially well-ordered on `s`, then `List.SublistForall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
* `Set.wellFoundedOn_iff` relates `well_founded_on` to the well-foundedness of a relation on the
  original type, to avoid dealing with subtypes.
* `Set.IsWF.mono` shows that a subset of a well-founded subset is well-founded.
* `Set.IsWF.union` shows that the union of two well-founded subsets is well-founded.
* `Finset.isWF` shows that all `Finset`s are well-founded.

## TODO

* Prove that `s` is partially well-ordered iff it has no infinite descending chain or antichain.
* Rename `Set.PartiallyWellOrderedOn` to `Set.WellQuasiOrderedOn` and `Set.IsPWO` to `Set.IsWQO`.

## References
* [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
* [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/

assert_not_exists IsOrderedRing

open scoped Function -- required for scoped `on` notation

variable {ι α β γ : Type*} {π : ι → Type*}

namespace Set

/-! ### Relations well-founded on sets -/

def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded (Subrel r (· ∈ s))
