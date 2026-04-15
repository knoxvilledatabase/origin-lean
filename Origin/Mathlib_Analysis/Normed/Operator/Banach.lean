/-
Extracted from Analysis/Normed/Operator/Banach.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

open Function Metric Set Filter Finset Topology NNReal

open LinearMap (range ker)

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E →SL[σ] F)

namespace ContinuousLinearMap

structure NonlinearRightInverse where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : F → E
  /-- The bound `C` so that `‖inverse x‖ ≤ C * ‖x‖` for all `x`. -/
  nnnorm : ℝ≥0
  bound' : ∀ y, ‖toFun y‖ ≤ nnnorm * ‖y‖
  right_inv' : ∀ y, f (toFun y) = y

-- INSTANCE (free from Core): :
