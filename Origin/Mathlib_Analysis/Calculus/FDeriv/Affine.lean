/-
Extracted from Analysis/Calculus/FDeriv/Affine.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The derivative of continuous affine maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
continuous affine maps.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (f : E →ᴬ[𝕜] F) {x : E} {s : Set E} {L : Filter (E × E)}

namespace ContinuousAffineMap

/-!
### Continuous affine maps
-/

protected theorem hasFDerivAtFilter : HasFDerivAtFilter f f.contLinear L := by
  refine .of_isLittleOTVS <| .congr_left (.zero _ _) ?_
  simp [(vsub_eq_sub _ _).symm.trans (f.contLinear_map_vsub _ _).symm]
