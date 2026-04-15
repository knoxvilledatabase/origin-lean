/-
Extracted from Order/Filter/Partial.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# `Tendsto` for relations and partial functions

This file generalizes `Filter` definitions from functions to partial functions and relations.

## Considering functions and partial functions as relations

A function `f : α → β` can be considered as the relation `Rel α β` which relates `x` and `f x` for
all `x`, and nothing else. This relation is called `Function.Graph f`.

A partial function `f : α →. β` can be considered as the relation `Rel α β` which relates `x` and
`f x` for all `x` for which `f x` exists, and nothing else. This relation is called
`PFun.Graph' f`.

In this regard, a function is a relation for which every element in `α` is related to exactly one
element in `β` and a partial function is a relation for which every element in `α` is related to at
most one element in `β`.

This file leverages this analogy to generalize `Filter` definitions from functions to partial
functions and relations.

## Notes

`Set.preimage` can be generalized to relations in two ways:
* `Rel.preimage` returns the image of the set under the inverse relation.
* `Rel.core` returns the set of elements that are only related to those in the set.

Both generalizations are sensible in the context of filters, so `Filter.comap` and `Filter.Tendsto`
get two generalizations each.

We first take care of relations. Then the definitions for partial functions are taken as special
cases of the definitions for relations.
-/

universe u v w

namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w}

open Filter

/-! ### Relations -/

def rmap (r : SetRel α β) (l : Filter α) : Filter β where
  sets := { s | r.core s ∈ l }
  univ_sets := by simp
  sets_of_superset hs st := mem_of_superset hs (SetRel.core_mono st)
  inter_sets hs ht := by
    simp only [Set.mem_setOf_eq]
    convert inter_mem hs ht
    rw [← SetRel.core_inter]
