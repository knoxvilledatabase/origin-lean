/-
Extracted from Analysis/SpecialFunctions/Trigonometric/ComplexDeriv.lean
Genuine: 3 | Conflates: 0 | Dissolved: 5 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.
-/

noncomputable section

namespace Complex

open Set Filter

open scoped Real

-- DISSOLVED: hasStrictDerivAt_tan

-- DISSOLVED: hasDerivAt_tan

open scoped Topology

theorem tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] x) atTop := by
  simp only [tan_eq_sin_div_cos, ← norm_eq_abs, norm_div]
  have A : sin x ≠ 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[≠] x) (𝓝[≠] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_punctured_nhds (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsWithin_zero.comp B).inv_tendsto_zero

theorem tendsto_abs_tan_atTop (k : ℤ) :
    Tendsto (fun x => abs (tan x)) (𝓝[≠] ((2 * k + 1) * π / 2 : ℂ)) atTop :=
  tendsto_abs_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩

-- DISSOLVED: continuousAt_tan

-- DISSOLVED: differentiableAt_tan

@[simp]
theorem deriv_tan (x : ℂ) : deriv tan x = 1 / cos x ^ 2 :=
  if h : cos x = 0 then by
    have : ¬DifferentiableAt ℂ tan x := mt differentiableAt_tan.1 (Classical.not_not.2 h)
    simp [deriv_zero_of_not_differentiableAt this, h, sq]
  else (hasDerivAt_tan h).deriv

-- DISSOLVED: contDiffAt_tan

end Complex
