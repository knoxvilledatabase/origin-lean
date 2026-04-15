/-
Extracted from Analysis/SpecialFunctions/Trigonometric/ArctanDeriv.lean
Genuine: 2 of 6 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core

/-!
# Derivatives of the `tan` and `arctan` functions.

Continuity and derivatives of the tangent and arctangent functions.
-/

noncomputable section

namespace Real

open Set Filter

open scoped Topology Real

-- DISSOLVED: hasStrictDerivAt_tan

-- DISSOLVED: hasDerivAt_tan

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] x) atTop := by
  have hx : Complex.cos x = 0 := mod_cast hx
  simp only [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_tan]
  refine (Complex.tendsto_norm_tan_of_cos_eq_zero hx).comp ?_
  refine Tendsto.inf Complex.continuous_ofReal.continuousAt ?_
  exact tendsto_principal_principal.2 fun y => mt Complex.ofReal_inj.1

theorem tendsto_abs_tan_atTop (k : ℤ) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2)) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

-- DISSOLVED: continuousAt_tan

-- DISSOLVED: differentiableAt_tan
