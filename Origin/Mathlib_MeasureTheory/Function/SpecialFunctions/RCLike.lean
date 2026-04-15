/-
Extracted from MeasureTheory/Function/SpecialFunctions/RCLike.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measurability of the basic `RCLike` functions

-/

noncomputable section

open NNReal ENNReal

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

theorem measurable_re : Measurable (re : 𝕜 → ℝ) :=
  continuous_re.measurable

theorem measurable_im : Measurable (im : 𝕜 → ℝ) :=
  continuous_im.measurable

end RCLike

section RCLikeComposition

variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {f : α → 𝕜}
  {μ : MeasureTheory.Measure α}
