/-
Extracted from Analysis/SpecificLimits/RCLike.lean
Genuine: 1 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# A collection of specific limit computations for `RCLike`

-/

open Set Algebra Filter

open scoped Topology

variable (𝕜 : Type*) [RCLike 𝕜]

theorem RCLike.tendsto_inverse_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert tendsto_algebraMap_inverse_atTop_nhds_zero_nat 𝕜
  simp

variable {𝕜}

-- DISSOLVED: RCLike.tendsto_add_mul_div_add_mul_atTop_nhds
