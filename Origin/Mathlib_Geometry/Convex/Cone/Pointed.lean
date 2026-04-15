/-
Extracted from Geometry/Convex/Cone/Pointed.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Pointed cones

A *pointed cone* is defined to be a submodule of a module where the scalars are restricted to be
nonnegative. This is equivalent to saying that, as a set, a pointed cone is a convex cone which
contains `0`. This is a bundled version of `ConvexCone.Pointed`. We choose the submodule definition
as it allows us to use the `Module` API to work with convex cones.

-/

assert_not_exists TopologicalSpace Real Cardinal

variable {R E F G : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

abbrev PointedCone (R E)
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E] :=
  Submodule {c : R // 0 ≤ c} E

namespace PointedCone

open Function Submodule

section Submodule

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [AddCommMonoid E] [Module R E]

variable {C : PointedCone R E}

set_option backward.isDefEq.respectTransparency false in
