/-
Extracted from Topology/Category/Sequential.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# The category of sequential topological spaces

We define the category `Sequential` of sequential topological spaces. We follow the usual template
for defining categories of topological spaces, by giving it the induced category structure from
`TopCat`.
-/

open CategoryTheory

universe u

structure Sequential where
  /-- The underlying topological space of an object of `Sequential`. -/
  toTop : TopCat.{u} -- TODO: turn this into `extends`
  /-- The underlying topological space is sequential. -/
  [is_sequential : SequentialSpace toTop]

namespace Sequential

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

attribute [instance] is_sequential

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (X : Type u) [TopologicalSpace X] [SequentialSpace X]

abbrev of : Sequential.{u} where
  toTop := TopCat.of X
  is_sequential := ‹_›
