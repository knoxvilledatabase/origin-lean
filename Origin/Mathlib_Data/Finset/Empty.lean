/-
Extracted from Data/Finset/Empty.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Empty and nonempty finite sets

This file defines the empty finite set ∅ and a predicate for nonempty `Finset`s.

## Main declarations
* `Finset.Nonempty`: A finset is nonempty if it has elements. This is equivalent to saying `s ≠ ∅`.
* `Finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Nonempty -/

protected def Nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s
