/-
Extracted from Analysis/Calculus/Deriv/Inv.lean
Genuine: 1 of 5 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

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

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

-- DISSOLVED: hasStrictDerivAt_inv

-- DISSOLVED: hasDerivAt_inv

-- DISSOLVED: hasDerivWithinAt_inv

-- DISSOLVED: differentiableAt_inv_iff

theorem deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with (rfl | hne)
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_inv_iff.1 (not_not.2 rfl))]
    simp
  · exact (hasDerivAt_inv hne).deriv
