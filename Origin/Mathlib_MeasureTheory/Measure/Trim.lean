/-
Extracted from MeasureTheory/Measure/Trim.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Restriction of a measure to a sub-σ-algebra


## Main definitions

* `MeasureTheory.Measure.trim`: restriction of a measure to a sub-sigma algebra.

-/

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*}

noncomputable

def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))
