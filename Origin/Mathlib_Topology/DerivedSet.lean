/-
Extracted from Topology/DerivedSet.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Derived set

This file defines the derived set of a set, the set of all `AccPt`s of its principal filter,
and proves some properties of it.

-/

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

def derivedSet (A : Set X) : Set X := {x | AccPt x (𝓟 A)}
