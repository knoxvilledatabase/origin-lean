/-
Extracted from Data/Finset/Erase.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Erasing an element from a finite set

## Main declarations

* `Finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.erase a⟩
