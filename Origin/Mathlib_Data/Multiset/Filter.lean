/-
Extracted from Data/Multiset/Filter.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Filtering multisets by a predicate

## Main definitions

* `Multiset.filter`: `filter p s` is the multiset of elements in `s` that satisfy `p`.
* `Multiset.filterMap`: `filterMap f s` is the multiset of `b`s where `some b ∈ map f s`.
-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.filter` -/

variable (p : α → Prop) [DecidablePred p]

def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (List.filter p l : Multiset α)) fun _l₁ _l₂ h => Quot.sound <| h.filter p
