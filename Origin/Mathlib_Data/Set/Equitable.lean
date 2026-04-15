/-
Extracted from Data/Set/Equitable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equitable functions

This file defines equitable functions.

A function `f` is equitable on a set `s` if `f a₁ ≤ f a₂ + 1` for all `a₁, a₂ ∈ s`. This is mostly
useful when the codomain of `f` is `ℕ` or `ℤ` (or more generally a successor order).

## TODO

`ℕ` can be replaced by any `SuccOrder` + `ConditionallyCompleteMonoid`, but we don't have the
latter yet.
-/

variable {α β : Type*}

namespace Set

def EquitableOn [LE β] [Add β] [One β] (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ + 1
