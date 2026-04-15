/-
Extracted from Analysis/LocallyConvex/Polar.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.polar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.polar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_bipolar`: The polar is a subset of the bipolar.
* `LinearMap.polar_isClosed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

variable {𝕜 E F : Type*}

open Topology

namespace LinearMap

section NormedRing

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]

variable [Module 𝕜 E] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

def polar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, ‖B x y‖ ≤ 1 }

theorem polar_mem (s : Set E) (y : F) (hy : y ∈ B.polar s) : ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  hy

theorem polar_eq_biInter_preimage (s : Set E) :
    B.polar s = ⋂ x ∈ s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1) := by aesop

theorem polar_isClosed (s : Set E) : IsClosed (X := WeakBilin B.flip) (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)
