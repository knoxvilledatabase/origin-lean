/-
Extracted from Data/Set/Defs.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Sets

This file sets up the theory of sets whose elements have a given type.

## Main definitions

Given a type `X` and a predicate `p : X → Prop`:

* `Set X` : the type of sets whose elements have type `X`
* `{a : X | p a} : Set X` : the set of all elements of `X` satisfying `p`
* `{a | p a} : Set X` : a more concise notation for `{a : X | p a}`
* `{f x y | (x : X) (y : Y)} : Set Z` : a more concise notation for `{z : Z | ∃ x y, f x y = z}`
* `{a ∈ S | p a} : Set X` : given `S : Set X`, the subset of `S` consisting of
  its elements satisfying `p`.

## Implementation issues

As in Lean 3, `Set X := X → Prop`
This file is a port of the core Lean 3 file `lib/lean/library/init/data/set.lean`.

-/

open Lean Elab Term Meta Batteries.ExtendedBinder

universe u

variable {α : Type u}

def Set (α : Type u) := α → Prop

attribute [to_dual_dont_translate] Set

def setOf {α : Type u} (p : α → Prop) : Set α :=
  p

namespace Set

protected def Mem (s : Set α) (a : α) : Prop :=
  s a

-- INSTANCE (free from Core): :
