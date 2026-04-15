/-
Extracted from Data/Multiset/Sum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `Multiset (α ⊕ β)`. Beware not to confuse
with the `Multiset.sum` operation which computes the additive sum.

## Main declarations

* `Multiset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/

open Sum

namespace Multiset

variable {α β γ : Type*} (s : Multiset α) (t : Multiset β)

def disjSum : Multiset (α ⊕ β) :=
  s.map inl + t.map inr
