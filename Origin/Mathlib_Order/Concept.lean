/-
Extracted from Order/Concept.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
* [Birkhoff, Garrett *Lattice Theory*][birkhoff1940]

## Tags

concept, formal concept analysis, intent, extent, object, attribute
-/

open Function OrderDual Order Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Lower and upper polars -/

def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }
