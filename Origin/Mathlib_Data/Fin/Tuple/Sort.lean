/-
Extracted from Data/Fin/Tuple/Sort.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Sorting tuples by their values

Given an `n`-tuple `f : Fin n → α` where `α` is ordered,
we may want to turn it into a sorted `n`-tuple.
This file provides an API for doing so, with the sorted `n`-tuple given by
`f ∘ Tuple.sort f`.

## Main declarations

* `Tuple.sort`: given `f : Fin n → α`, produces a permutation on `Fin n`
* `Tuple.monotone_sort`: `f ∘ Tuple.sort f` is `Monotone`

-/

namespace Tuple

variable {n : ℕ}

variable {α : Type*} [LinearOrder α]

def graph (f : Fin n → α) : Finset (α ×ₗ Fin n) :=
  Finset.univ.image fun i => (f i, i)

def graph.proj {f : Fin n → α} : graph f → α := fun p => p.1.1

set_option backward.isDefEq.respectTransparency false in
