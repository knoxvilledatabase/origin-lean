/-
Extracted from Data/Multiset/Bind.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bind operation for multisets

This file defines a few basic operations on `Multiset`, notably the monadic bind.

## Main declarations

* `Multiset.join`: The join, aka union or sum, of multisets.
* `Multiset.bind`: The bind of a multiset-indexed family of multisets.
* `Multiset.product`: Cartesian product of two multisets.
* `Multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/

assert_not_exists MonoidWithZero MulAction

universe v

variable {α : Type*} {β : Type v} {γ δ : Type*}

namespace Multiset

/-! ### Join -/

def join : Multiset (Multiset α) → Multiset α :=
  sum

theorem coe_join : ∀ L : List (List α), join (L.map ((↑) : List α → Multiset α) :
    Multiset (Multiset α)) = L.flatten
  | [] => rfl
  | l :: L => by
      exact congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)
