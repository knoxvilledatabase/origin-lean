/-
Extracted from Data/Finset/Sum.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
* `Finset.toLeft`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `α`.
* `Finset.toRight`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `β`.
-/

open Function Multiset Sum

namespace Finset

variable {α β γ : Type*} (s : Finset α) (t : Finset β)

def disjSum : Finset (α ⊕ β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩
