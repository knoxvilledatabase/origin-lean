/-
Extracted from Analysis/CStarAlgebra/Unitary/Connected.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # The unitary group in a unital C⋆-algebra is locally path connected

When `A` is a unital C⋆-algebra and `u : unitary A` is a unitary element whose distance to `1` is
less that `2`, the spectrum of `u` is contained in the slit plane, so the principal branch of the
logarithm is continuous on the spectrum of `u` (or equivalently, `Complex.arg` is continuous on the
spectrum). The continuous functional calculus can then be used to define a selfadjoint element `x`
such that `u = exp (I • x)`. Moreover, there is a relatively nice relationship between the norm of
`x` and the norm of `u - 1`, namely `‖u - 1‖ ^ 2 = 2 * (1 - cos ‖x‖)`. In fact, these maps `u ↦ x`
and `x ↦ u` establish a partial homeomorphism between `ball (1 : unitary A) 2` and
`ball (0 : selfAdjoint A) π`.

The map `t ↦ exp (t • (I • x))` constitutes a path from `1` to `u`, showing that unitary elements
sufficiently close (i.e., within a distance `2`) to `1 : unitary A` are path connected to `1`.
This property can be translated around the unitary group to show that if `u v : unitary A` are
unitary elements with `‖u - v‖ < 2`, then there is a path joining them. In fact, this path has the
property that it lies within `closedBall u ‖u - v‖`, and consequently any ball of radius `δ < 2` in
`unitary A` is path connected. Therefore, the unitary group is locally path connected.

Finally, we provide the standard characterization of the path component of `1 : unitary A` as finite
products of exponential unitaries.

## Main results

+ `Unitary.argSelfAdjoint`: the selfadjoint element obtained by taking the argument (using the
  principal branch and the continuous functional calculus) of a unitary. This returns `0` if
  the principal branch of the logarithm is not continuous on the spectrum of the unitary element.
+ `selfAdjoint.norm_sq_expUnitary_sub_one`:
  `‖(selfAdjoint.expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)`
+ `Unitary.norm_argSelfAdjoint`:
  `‖Unitary.argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)`
+ `Unitary.openPartialHomeomorph`: the maps `Unitary.argSelfAdjoint` and `selfAdjoint.expUnitary`
  form a partial homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
+ `selfAdjoint.expUnitaryPathToOne`: the path `t ↦ expUnitary (t • x)` from `1` to
  `expUnitary x` for a selfadjoint element `x`.
+ `Unitary.isPathConnected_ball`: any ball of radius `δ < 2` in the unitary group of a unital
  C⋆-algebra is path connected.
+ `Unitary.instLocPathConnectedSpace`: the unitary group of a C⋆-algebra is locally path connected.
+ `Unitary.mem_pathComponentOne_iff`: The path component of the identity in the unitary group of a
  C⋆-algebra is the set of unitaries that can be expressed as a product of exponentials of
  selfadjoint elements.
-/

variable {A : Type*} [CStarAlgebra A]

open Complex Metric NormedSpace selfAdjoint Unitary

open scoped Real

lemma Unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u ∈ unitary A)
    {z : ℂ} (hz : z ∈ spectrum ℂ u) :
    2 * (1 - z.re) ≤ ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  convert norm_apply_le_norm_cfc (fun z ↦ z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_eq_one this)).symm
