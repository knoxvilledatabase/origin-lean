/-
Extracted from Analysis/Calculus/Deriv/Inv.lean
Genuine: 3 of 25 | Dissolved: 22 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

universe u

open scoped Topology

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

-- DISSOLVED: hasStrictDerivAt_inv

-- DISSOLVED: hasDerivAt_inv

-- DISSOLVED: hasDerivWithinAt_inv

-- DISSOLVED: differentiableAt_inv_iff

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · simp [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
  · exact (hasDerivAt_inv hne).deriv

@[simp]
theorem deriv_inv' : (deriv fun x : 𝕜 => x⁻¹) = fun x => -(x ^ 2)⁻¹ :=
  funext fun _ => deriv_inv

-- DISSOLVED: derivWithin_inv

-- DISSOLVED: hasFDerivAt_inv

-- DISSOLVED: hasStrictFDerivAt_inv

-- DISSOLVED: hasFDerivWithinAt_inv

theorem fderiv_inv : fderiv 𝕜 (fun x => x⁻¹) x = smulRight (1 : 𝕜 →L[𝕜] 𝕜) (-(x ^ 2)⁻¹) := by
  rw [← deriv_fderiv, deriv_inv]

-- DISSOLVED: fderivWithin_inv

variable {c : 𝕜 → 𝕜} {c' : 𝕜}

-- DISSOLVED: HasDerivWithinAt.inv

-- DISSOLVED: HasDerivAt.inv

-- DISSOLVED: derivWithin_inv'

-- DISSOLVED: deriv_inv''

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

-- DISSOLVED: HasDerivWithinAt.div

-- DISSOLVED: HasStrictDerivAt.div

-- DISSOLVED: HasDerivAt.div

-- DISSOLVED: DifferentiableWithinAt.div

-- DISSOLVED: DifferentiableAt.div

-- DISSOLVED: DifferentiableOn.div

-- DISSOLVED: Differentiable.div

-- DISSOLVED: derivWithin_div

-- DISSOLVED: deriv_div

end Division
