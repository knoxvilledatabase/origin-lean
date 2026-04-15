/-
Extracted from Topology/Category/DeltaGenerated.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Delta-generated topological spaces

The category of delta-generated spaces.

See https://ncatlab.org/nlab/show/Delta-generated+topological+space.

Adapted from `Mathlib/Topology/Category/CompactlyGenerated.lean`.

## TODO
* `DeltaGenerated` is Cartesian closed.
-/

universe u

open CategoryTheory

structure DeltaGenerated where
  /-- the underlying topological space -/
  toTop : TopCat.{u}
  /-- The underlying topological space is delta-generated. -/
  deltaGenerated : DeltaGeneratedSpace toTop := by infer_instance

namespace DeltaGenerated

-- INSTANCE (free from Core): :

attribute [instance] deltaGenerated

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

abbrev of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} where
  toTop := TopCat.of X
  deltaGenerated := ‹_›
