/-
Extracted from MeasureTheory/Measure/Count.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Counting measure

In this file we define the counting measure `MeasureTheory.Measure.count`
as `MeasureTheory.Measure.sum MeasureTheory.Measure.dirac`
and prove basic properties of this measure.
-/

open Set

open scoped ENNReal Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

noncomputable section

namespace MeasureTheory.Measure

def count : Measure α :=
  sum dirac
