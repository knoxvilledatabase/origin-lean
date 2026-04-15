/-
Extracted from Topology/MetricSpace/IsometricSMul.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Group actions by isometries

In this file we define two typeclasses:

- `IsIsometricSMul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `IsIsometricVAdd` is an additive version of `IsIsometricSMul`.

We also prove basic facts about isometric actions and define bundled isometries
`IsometryEquiv.constSMul`, `IsometryEquiv.mulLeft`, `IsometryEquiv.mulRight`,
`IsometryEquiv.divLeft`, `IsometryEquiv.divRight`, and `IsometryEquiv.inv`, as well as their
additive versions.

If `G` is a group, then `IsIsometricSMul G G` means that `G` has a left-invariant metric while
`IsIsometricSMul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`NormedGroup`.
-/

open Set

open scoped ENNReal Pointwise

universe u v w

variable (M : Type u) (G : Type v) (X : Type w)

class IsIsometricVAdd (X : Type w) [PseudoEMetricSpace X] [VAdd M X] : Prop where
  isometry_vadd (X) : ∀ c : M, Isometry ((c +ᵥ ·) : X → X)
