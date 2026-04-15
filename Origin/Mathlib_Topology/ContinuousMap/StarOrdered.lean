/-
Extracted from Topology/ContinuousMap/StarOrdered.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-! # Continuous functions as a star-ordered ring

The type class `ContinuousSqrt` gives a sufficient condition on `R` to make `C(α, R)`
and `C(α, R)₀` into a `StarOrderedRing` for any topological space `α`, thereby providing a means
by which we can ensure `C(α, R)` has this property. This condition is satisfied
by `ℝ≥0`, `ℝ`, and `ℂ`, and the instances can be found in the file
`Mathlib/Topology/ContinuousMap/ContinuousSqrt.lean`.

## Implementation notes

Instead of asking for a well-behaved square root on `{x : R | 0 ≤ x}` in the obvious way, we instead
require that, for every `x y  : R` such that `x ≤ y`, there exist some `s` such that `x + s*s = y`.
This is because we need this type class to work for `ℝ≥0` for the
continuous functional calculus. We could instead assume `[OrderedSub R] [ContinuousSub R]`, but that
would lead to a proliferation of type class assumptions in the general case of the continuous
functional calculus, which we want to avoid because there is *already* a proliferation of type
classes there. At the moment, we only expect this class to be used in that context so this is a
reasonable compromise.

The field `ContinuousSqrt.sqrt` is data, which means that, if we implement an instance of the class
for a generic C⋆-algebra, we'll get a non-defeq diamond for the case `R := ℂ`. This shouldn't really
be a problem since the only purpose is to obtain the instance `StarOrderedRing C(α, R)`, which is a
`Prop`, but we note it for future reference.
-/

class ContinuousSqrt (R : Type*) [LE R] [NonUnitalSemiring R] [TopologicalSpace R] where
  /-- `sqrt (a, b)` returns a value `s` such that `b = a + s * s` when `a ≤ b`. -/
  protected sqrt : R × R → R
  protected continuousOn_sqrt : ContinuousOn sqrt {x | x.1 ≤ x.2}
  protected sqrt_nonneg (x : R × R) : x.1 ≤ x.2 → 0 ≤ sqrt x
  protected sqrt_mul_sqrt (x : R × R) : x.1 ≤ x.2 → x.2 = x.1 + sqrt x * sqrt x

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): {R

end ContinuousMap

namespace ContinuousMapZero

variable {α : Type*} [TopologicalSpace α] [Zero α]

-- INSTANCE (free from Core): instStarOrderedRing

end ContinuousMapZero
