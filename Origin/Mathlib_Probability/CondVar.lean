/-
Extracted from Probability/CondVar.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conditional variance

This file defines the variance of a real-valued random variable conditional to a sigma-algebra.

## TODO

Define the Lebesgue conditional variance. See
[GibbsMeasure](https://github.com/james18lpc/GibbsMeasure) for a definition of the Lebesgue
conditional expectation.
-/

open MeasureTheory Filter

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m₀ m m' : MeasurableSpace Ω} {hm : m ≤ m₀} {X Y : Ω → ℝ} {μ : Measure[m₀] Ω}
  {s : Set Ω}

variable (m X μ) in

noncomputable def condVar : Ω → ℝ := μ[(X - μ[X | m]) ^ 2 | m]
