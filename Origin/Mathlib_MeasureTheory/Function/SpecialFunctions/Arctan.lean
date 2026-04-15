/-
Extracted from MeasureTheory/Function/SpecialFunctions/Arctan.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measurability of arctan

-/

namespace Real

theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable

end Real

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}
