/-
Extracted from MeasureTheory/Measure/Dirac.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Dirac measure

In this file we define the Dirac measure `MeasureTheory.Measure.dirac a`
and prove some basic facts about it.
-/

open Function Set

open scoped ENNReal NNReal

noncomputable section

variable {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α} {a : α}

namespace MeasureTheory

namespace Measure

def dirac (a : α) : Measure α := (OuterMeasure.dirac a).toMeasure (by simp)

-- INSTANCE (free from Core): :

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _
