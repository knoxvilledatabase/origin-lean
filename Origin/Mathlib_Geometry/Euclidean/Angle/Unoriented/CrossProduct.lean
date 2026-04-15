/-
Extracted from Geometry/Euclidean/Angle/Unoriented/CrossProduct.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Norm of cross-products

This file proves `InnerProductGeometry.norm_withLpEquiv_crossProduct`, relating the norm of the
cross-product of two real vectors with their individual norms.
-/

open Matrix Real WithLp

namespace InnerProductGeometry

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false in

lemma norm_ofLp_crossProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖toLp 2 (ofLp a ⨯₃ ofLp b)‖ = ‖a‖ * ‖b‖ * sin (angle a b) := by
  have := sin_angle_nonneg a b
  refine sq_eq_sq₀ (by positivity) (by positivity) |>.mp ?_
  trans ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2
  · simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, cross_dot_cross, dotProduct_comm (ofLp b) (ofLp a), sq]
  · linear_combination (‖a‖ * ‖b‖) ^ 2 * (sin_sq_add_cos_sq (angle a b)).symm +
      congrArg (· ^ 2) (cos_angle_mul_norm_mul_norm a b)

lemma norm_toLp_symm_crossProduct (a b : Fin 3 → ℝ) :
    ‖toLp 2 (a ⨯₃ b)‖ = ‖toLp 2 a‖ * ‖toLp 2 b‖ * sin (angle (toLp 2 a) (toLp 2 b)) := by
  simp [← norm_ofLp_crossProduct (toLp 2 a) (toLp 2 b)]

end InnerProductGeometry
