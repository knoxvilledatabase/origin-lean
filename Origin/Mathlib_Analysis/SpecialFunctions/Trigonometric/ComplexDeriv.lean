/-
Extracted from Analysis/SpecialFunctions/Trigonometric/ComplexDeriv.lean
Genuine: 2 of 4 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

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

theorem tendsto_norm_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
    Tendsto (fun x => ‖tan x‖) (𝓝[≠] x) atTop := by
  simp only [tan_eq_sin_div_cos, norm_div]
  have A : sin x ≠ 0 := fun h => by simpa [*, sq] using sin_sq_add_cos_sq x
  have B : Tendsto cos (𝓝[≠] x) (𝓝[≠] 0) :=
    hx ▸ (hasDerivAt_cos x).tendsto_nhdsNE (neg_ne_zero.2 A)
  exact continuous_sin.continuousWithinAt.norm.pos_mul_atTop (norm_pos_iff.2 A)
    (tendsto_norm_nhdsNE_zero.comp B).inv_tendsto_nhdsGT_zero

theorem tendsto_norm_tan_atTop (k : ℤ) :
    Tendsto (fun x => ‖tan x‖) (𝓝[≠] ((2 * k + 1) * π / 2 : ℂ)) atTop :=
  tendsto_norm_tan_of_cos_eq_zero <| cos_eq_zero_iff.2 ⟨k, rfl⟩
