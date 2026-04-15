/-
Extracted from Analysis/Normed/Module/Span.lean
Genuine: 2 of 10 | Dissolved: 7 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The span of a single vector

The equivalence of `𝕜` and `𝕜 • x` for `x ≠ 0` are defined as continuous linear equivalence and
isometry.

## Main definitions

* `ContinuousLinearEquiv.toSpanNonzeroSingleton`: The continuous linear equivalence between `𝕜` and
`𝕜 • x` for `x ≠ 0`.
* `LinearIsometryEquiv.toSpanUnitSingleton`: For `‖x‖ = 1` the continuous linear equivalence is a
linear isometry equivalence.

-/

variable {𝕜 E : Type*}

namespace LinearMap

variable (𝕜)

section Seminormed

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by
  rw [mul_comm]
  exact norm_smul _ _

end Seminormed

end LinearMap

namespace ContinuousLinearEquiv

variable (𝕜)

section Seminormed

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

-- DISSOLVED: _root_.LinearEquiv.toSpanNonzeroSingleton_homothety

end Seminormed

section Normed

variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- DISSOLVED: toSpanNonzeroSingleton

-- DISSOLVED: coord

-- DISSOLVED: coe_toSpanNonzeroSingleton_symm

-- DISSOLVED: coord_toSpanNonzeroSingleton

-- DISSOLVED: toSpanNonzeroSingleton_coord

-- DISSOLVED: coord_self

end Normed

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]

noncomputable def toSpanUnitSingleton (x : E) (hx : ‖x‖ = 1) :
    𝕜 ≃ₗᵢ[𝕜] 𝕜 ∙ x where
  toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton 𝕜 E x (by aesop)
  norm_map' := by
    intro
    rw [LinearEquiv.toSpanNonzeroSingleton_homothety, hx, one_mul]

@[simp] theorem toSpanUnitSingleton_apply (x : E) (hx : ‖x‖ = 1) (r : 𝕜) :
    toSpanUnitSingleton x hx r = (⟨r • x, by aesop⟩ : 𝕜 ∙ x) := by
  rfl

end LinearIsometryEquiv
