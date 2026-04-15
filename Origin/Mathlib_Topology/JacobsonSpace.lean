/-
Extracted from Topology/JacobsonSpace.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Jacobson spaces

## Main results
- `JacobsonSpace`: The class of Jacobson spaces, i.e.
  spaces such that the set of closed points are dense in every closed subspace.
- `jacobsonSpace_iff_locallyClosed`:
  `X` is a Jacobson space iff every locally closed subset contains a closed point of `X`.
- `JacobsonSpace.discreteTopology`:
  If `X` only has finitely many closed points, then the topology on `X` is discrete.

## References
- https://stacks.math.columbia.edu/tag/005T

-/

open Topology TopologicalSpace

variable (X) {Y} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

section closedPoints

def closedPoints : Set X := setOf (IsClosed {·})

variable {X}
