/-
Extracted from Analysis/Normed/Operator/Prod.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Operator norm: Cartesian products

Interaction of operator norm with Cartesian products.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]

open Set Real Metric ContinuousLinearMap

section SemiNormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

namespace ContinuousLinearMap

section FirstSecond

variable (𝕜 E F)

lemma norm_fst_le : ‖fst 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using le_max_left ‖e‖ ‖f‖)

lemma norm_snd_le : ‖snd 𝕜 E F‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun ⟨e, f⟩ ↦ by simpa only [one_mul] using le_max_right ‖e‖ ‖f‖)

end FirstSecond

section OpNorm
