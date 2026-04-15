/-
Extracted from Topology/Category/FinTopCat.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Category of finite topological spaces

Definition of the category of finite topological spaces with the canonical
forgetful functors.

-/

universe u

open CategoryTheory

structure FinTopCat where
  /-- carrier of a finite topological space. -/
  toTop : TopCat.{u} -- TODO: turn this into an `extends`?
  [fintype : Fintype toTop]

namespace FinTopCat

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

attribute [instance] fintype

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def of (X : Type u) [Fintype X] [TopologicalSpace X] : FinTopCat where
  toTop := TopCat.of X
  fintype := ‹_›
