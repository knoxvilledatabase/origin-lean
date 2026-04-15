/-
Extracted from Data/Set/Basic.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `Set X := X → Prop`. Note that this function need not
be decidable. The definition is in the module `Mathlib/Data/Set/Defs.lean`.

This file provides some basic definitions related to sets and functions not present in the
definitions file, as well as extra lemmas for functions defined in the definitions file and
`Mathlib/Data/Set/Operations.lean` (empty set, univ, union, intersection, insert, singleton and
powerset).

Note that a set is a term, not a type. There is a coercion from `Set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the directory `Mathlib/SetTheory/ZFC/`, which contains an encoding of ZFC set theory in
Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : Set α` and `s₁ s₂ : Set α` are subsets of `α`

-  `t : Set β` is a subset of `β`.

Definitions in the file:

* `Nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Implementation notes

* `s.Nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
  the `s.Nonempty` dot notation can be used.

* For `s : Set α`, do not use `Subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, union, intersection, insert, singleton, powerset
-/

assert_not_exists HeytingAlgebra RelIso

/-! ### Set coercion to a type -/

open Function

universe u v

namespace Set

variable {α : Type u} {s t : Set α}

protected theorem mem_injective : Injective (Membership.mem : Set α → α → Prop) := injective_id

protected theorem mem_surjective : Surjective (Membership.mem : Set α → α → Prop) := surjective_id

protected theorem mem_bijective : Bijective (Membership.mem : Set α → α → Prop) := bijective_id

-- INSTANCE (free from Core): instDistribLattice

-- INSTANCE (free from Core): instBoundedOrder

-- INSTANCE (free from Core): :
