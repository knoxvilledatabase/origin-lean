/-
Extracted from Analysis/SpecificLimits/RCLike.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A collection of specific limit computations for `RCLike`

-/

open Set Algebra Filter

open scoped Topology

namespace RCLike

variable (𝕜 : Type*) [RCLike 𝕜]

theorem tendsto_ofReal_cobounded_cobounded :
    Tendsto ofReal (Bornology.cobounded ℝ) (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_norm_cobounded_atTop)

theorem tendsto_ofReal_atTop_cobounded :
    Tendsto ofReal atTop (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atTop_atTop)

theorem tendsto_ofReal_atBot_cobounded :
    Tendsto ofReal atBot (Bornology.cobounded 𝕜) :=
  tendsto_norm_atTop_iff_cobounded.mp (mod_cast tendsto_abs_atBot_atTop)

end RCLike
