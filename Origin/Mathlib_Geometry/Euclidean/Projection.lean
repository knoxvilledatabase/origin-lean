/-
Extracted from Geometry/Euclidean/Projection.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Orthogonal projection in affine spaces

This file defines orthogonal projection onto an affine subspace,
and reflection of a point in an affine subspace.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

-/

noncomputable section

namespace EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace 𝕜 V₂]

open AffineSubspace

variable [MetricSpace P] [NormedAddTorsor V P]

def orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P →ᴬ[𝕜] s :=
  letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
    |>.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjection.toContinuousAffineMap
    |>.comp <| AffineIsometryEquiv.vaddConst 𝕜 (x : P) |>.symm

theorem orthogonalProjection_apply_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p x} (hx : x ∈ s) :
    orthogonalProjection s p = (s.direction.orthogonalProjection (p -ᵥ x) : V) +ᵥ x := by
  rw [orthogonalProjection_apply, coe_vadd, vadd_eq_vadd_iff_sub_eq_vsub, ← Submodule.coe_sub,
    ← map_sub, vsub_sub_vsub_cancel_left, Submodule.coe_orthogonalProjection_apply,
    Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx
