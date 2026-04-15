/-
Extracted from Geometry/Euclidean/Angle/Unoriented/Conformal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

namespace InnerProductGeometry

variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem ConformalAt.preserves_angle {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x)
    (H : ConformalAt f x) (u v : E) : angle (f' u) (f' v) = angle u v :=
  let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v

end InnerProductGeometry
