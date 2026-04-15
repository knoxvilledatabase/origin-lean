/-
Extracted from Geometry/Euclidean/Angle/Unoriented/Basic.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Angles between vectors

This file defines unoriented angles in real inner product spaces.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.
-/

assert_not_exists HasFDerivAt ConformalAt

noncomputable section

open Real Set

open RealInnerProductSpace

namespace InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {x y : V}

def angle (x y : V) : ℝ :=
  Real.arccos (⟪x, y⟫ / (‖x‖ * ‖y‖))

-- DISSOLVED: continuousAt_angle

-- DISSOLVED: angle_smul_smul
