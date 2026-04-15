/-
Extracted from Analysis/Normed/Operator/NNNorm.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operator norm as an `NNNorm`

Operator norm as an `NNNorm`, i.e. taking values in non-negative reals.

-/

suppress_compilation

open Bornology

open Filter hiding map_smul

open scoped NNReal Topology Uniformity

open Metric ContinuousLinearMap

open Set Real

variable {𝕜 𝕜₂ 𝕜₃ E F G : Type*}

section NontriviallySemiNormed

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]

variable {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]

namespace ContinuousLinearMap

theorem nnnorm_def (f : E →SL[σ₁₂] F) : ‖f‖₊ = sInf { c | ∀ x, ‖f x‖₊ ≤ c * ‖x‖₊ } := by
  ext
  rw [NNReal.coe_sInf, coe_nnnorm, norm_def, NNReal.coe_image]
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, mem_setOf_eq, NNReal.coe_mk,
    exists_prop]
