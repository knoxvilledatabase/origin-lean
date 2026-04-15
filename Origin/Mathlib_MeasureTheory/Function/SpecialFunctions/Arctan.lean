/-
Extracted from MeasureTheory/Function/SpecialFunctions/Arctan.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of arctan

-/

namespace Real

@[measurability]
theorem measurable_arctan : Measurable arctan :=
  continuous_arctan.measurable

end Real

section RealComposition

open Real

variable {α : Type*} {m : MeasurableSpace α} {f : α → ℝ}

@[measurability]
theorem Measurable.arctan (hf : Measurable f) : Measurable fun x => arctan (f x) :=
  measurable_arctan.comp hf

end RealComposition
