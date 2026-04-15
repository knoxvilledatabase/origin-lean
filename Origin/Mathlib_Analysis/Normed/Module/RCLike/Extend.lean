/-
Extracted from Analysis/Normed/Module/RCLike/Extend.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `StrongDual.extendRCLike` preserves the norm of the functional.
-/

open RCLike ContinuousLinearMap

open scoped ComplexConjugate

namespace StrongDual

variable {𝕜 F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

variable [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

theorem norm_extendRCLike_bound (fr : StrongDual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  set lm : StrongDual 𝕜 F := fr.extendRCLike
  by_cases h : lm x = 0
  · rw [h, norm_zero]
    positivity
  rw [← mul_le_mul_iff_right₀ (norm_pos_iff.2 h), ← sq]
  calc
    ‖lm x‖ ^ 2 = fr (conj (lm x : 𝕜) • x) := Module.Dual.norm_extendRCLike_apply_sq fr.toLinearMap x
    _ ≤ ‖fr (conj (lm x : 𝕜) • x)‖ := le_abs_self _
    _ ≤ ‖fr‖ * ‖conj (lm x : 𝕜) • x‖ := le_opNorm _ _
    _ = ‖(lm x : 𝕜)‖ * (‖fr‖ * ‖x‖) := by rw [norm_smul, norm_conj, mul_left_comm]
