/-
Extracted from MeasureTheory/Measure/Real.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measures as real-valued functions

Given a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.
In this file, we develop a basic API around this notion.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of
the form `≠ ∞`.

There are certainly many missing lemmas. The missing ones should be added as they are needed.

There are no lemmas on infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. They should probably be added in the long
run.
-/

open MeasureTheory Measure Set

open scoped ENNReal NNReal Function symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}

theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

-- DISSOLVED: measureReal_ne_zero_iff
