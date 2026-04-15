/-
Extracted from Analysis/Calculus/AddTorsor/AffineMap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth

-/

namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]

variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

end ContinuousAffineMap
