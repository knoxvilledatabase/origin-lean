/-
Extracted from Analysis/Normed/Module/Alternating/Curry.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Currying continuous alternating forms

In this file we define `ContinuousAlternatingMap.curryLeft`
which interprets a continuous alternating map in `n + 1` variables
as a continuous linear map in the 0th variable
taking values in the continuous alternating maps in `n` variables.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

namespace ContinuousAlternatingMap

noncomputable def curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le
