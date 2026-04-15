/-
Extracted from Data/Multiset/MapFold.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Mapping and folding multisets

## Main definitions

* `Multiset.map`: `map f s` applies `f` to each element of `s`.
* `Multiset.foldl`: `foldl f b s` picks elements out of `s` and applies `f (f ... b x₁) x₂`.
* `Multiset.foldr`: `foldr f b s` picks elements out of `s` and applies `f x₁ (f ... x₂ b)`.

## TODO

Many lemmas about `Multiset.map` are proven in `Mathlib/Data/Multiset/Filter.lean`:
should we switch the import direction?

-/

assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.map` -/

def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)
