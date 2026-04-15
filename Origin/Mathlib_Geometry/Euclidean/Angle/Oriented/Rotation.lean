/-
Extracted from Geometry/Euclidean/Angle/Oriented/Rotation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/

noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}

variable [NormedAddCommGroup V] [NormedAddCommGroup V']

variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']

variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "J" => o.rightAngleRotation

def rotationAux (θ : Real.Angle) : V →ₗᵢ[ℝ] V :=
  LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination ⟪x, y⟫ * θ.cos_sq_add_sin_sq)
