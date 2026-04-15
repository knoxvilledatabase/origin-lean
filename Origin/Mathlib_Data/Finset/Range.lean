/-
Extracted from Data/Finset/Range.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite sets made of a range of elements.

## Main declarations

### Finset constructions

* `Finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ..., n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.

## Tags

finite sets, finset

-/

assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

open Multiset Subtype Function

/-! ### range -/

section Range

open Nat

variable {n m l : ℕ}

def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩
