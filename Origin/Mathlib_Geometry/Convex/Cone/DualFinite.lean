/-
Extracted from Geometry/Convex/Cone/DualFinite.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Duals of finitely generated cones

This file defines the notion of dually finitely generated cones. A cone is dually finitely
generated (or `DualFG` for short) if it is the dual of a finite set, or equivalently, of a
finitely generated cone. In geometric terms, a cone is dually finitely generated if it can
be written as the intersection of finitely many halfspaces. This is also known as an H-cone.
This is the counterpart to `FG` (finitely generated) which states that the cone is the conic hull
of a finite set, or a V-cone.

In finite dimensional vector spaces, `FG` is equivalent to `DualFG` by the Minkowski-Weyl theorem.
In this case, V- and H-cones are known as polyhedral cones.

## Main declarations

- `PointedCone.DualFG` expresses that a cone is the dual of a finite set.

-/

namespace PointedCone

variable {R M N : Type*}

variable [CommRing R] [PartialOrder R] [IsOrderedRing R]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in

def DualFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C
