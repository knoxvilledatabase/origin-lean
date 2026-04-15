/-
Extracted from Analysis/Calculus/FDeriv/RestrictScalars.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The derivative of the scalar restriction of a linear map

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
the scalar restriction of a linear map.
-/

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]

variable [IsScalarTower 𝕜 𝕜' E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]

variable [IsScalarTower 𝕜 𝕜' F]

variable {f : E → F} {f' : E →L[𝕜'] F} {s : Set E} {x : E}

theorem HasFDerivAtFilter.restrictScalars {L} (h : HasFDerivAtFilter f f' L) :
    HasFDerivAtFilter f (f'.restrictScalars 𝕜) L :=
  .of_isLittleO h.isLittleO
