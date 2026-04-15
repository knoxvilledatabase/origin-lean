/-
Extracted from Topology/ContinuousMap/ContinuousMapZero.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous maps sending zero to zero

This is the type of continuous maps from `X` to `R` such that `(0 : X) ↦ (0 : R)` for which we
provide the scoped notation `C(X, R)₀`.  We provide this as a dedicated type solely for the
non-unital continuous functional calculus, as using various terms of type `Ideal C(X, R)` were
overly burdensome on type class synthesis.

Of course, one could generalize to maps between pointed topological spaces, but that goes beyond
the purpose of this type.
-/

assert_not_exists StarOrderedRing

open Function Set Topology

structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero
