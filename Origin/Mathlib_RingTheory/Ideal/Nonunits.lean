/-
Extracted from RingTheory/Ideal/Nonunits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The set of non-invertible elements of a monoid

## Main definitions

* `nonunits` is the set of non-invertible elements of a monoid.

## Main results

* `exists_max_ideal_of_mem_nonunits`: every element of `nonunits` is contained in a maximal ideal
-/

variable {F α β : Type*} {a b : α}

def nonunits (α : Type*) [Monoid α] : Set α :=
  { a | ¬IsUnit a }
