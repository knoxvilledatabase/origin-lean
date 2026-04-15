/-
Extracted from Topology/Algebra/Module/Spaces/WeakDual.lean
Genuine: 2 of 9 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Weak dual topology

We continue in the setting of `Mathlib/Topology/Algebra/Module/WeakBilin.lean`,
which defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In this file, we consider two special cases.
In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakDual 𝕜 E` and `WeakSpace 𝕜 E`,
with the respective topology instances on it.

* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/

noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 E F : Type*}

def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)

deriving AddCommMonoid, TopologicalSpace, ContinuousAdd, Inhabited,

  FunLike, ContinuousLinearMapClass

namespace WeakDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

-- INSTANCE (free from Core): instMulAction

-- INSTANCE (free from Core): instDistribMulAction

-- INSTANCE (free from Core): instContinuousConstSMul

-- INSTANCE (free from Core): instContinuousSMul

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): instModule

end WeakDual

namespace StrongDual

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

def toWeakDual : StrongDual 𝕜 E ≃ₗ[𝕜] WeakDual 𝕜 E :=
  LinearEquiv.refl 𝕜 (StrongDual 𝕜 E)
