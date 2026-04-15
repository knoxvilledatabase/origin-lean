/-
Extracted from MeasureTheory/Integral/Average.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral average of a function

In this file we define `MeasureTheory.average μ f` (notation: `⨍ x, f x ∂μ`) to be the average
value of `f` with respect to measure `μ`. It is defined as `∫ x, f x ∂((μ univ)⁻¹ • μ)`, so it
is equal to zero if `f` is not integrable or if `μ` is an infinite measure. If `μ` is a probability
measure, then the average of any function is equal to its integral.

For the average on a set, we use `⨍ x in s, f x ∂μ` (notation for `⨍ x, f x ∂(μ.restrict s)`). For
average w.r.t. the volume, one can omit `∂volume`.

Both have a version for the Lebesgue integral rather than Bochner.

We prove several versions of the first moment method: An integrable function is below/above its
average on a set of positive measure:
* `measure_le_setLAverage_pos` for the Lebesgue integral
* `measure_le_setAverage_pos` for the Bochner integral

## Implementation notes

The average is defined as an integral over `(μ univ)⁻¹ • μ` so that all theorems about Bochner
integrals work for the average without modifications. For theorems that require integrability of a
function, we provide a convenience lemma `MeasureTheory.Integrable.to_average`.

## Tags

integral, center mass, average value, set average
-/

open ENNReal MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E F : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ ν : Measure α}
  {s t : Set α}

/-!
### Average value of a function w.r.t. a measure

The (Bochner, Lebesgue) average value of a function `f` w.r.t. a measure `μ` (notation:
`⨍ x, f x ∂μ`, `⨍⁻ x, f x ∂μ`) is defined as the (Bochner, Lebesgue) integral divided by the total
measure, so it is equal to zero if `μ` is an infinite measure, and (typically) equal to infinity if
`f` is not integrable. If `μ` is a probability measure, then the average of any function is equal to
its integral.
-/

namespace MeasureTheory

section ENNReal

variable (μ) {f g : α → ℝ≥0∞}

noncomputable def laverage (f : α → ℝ≥0∞) := ∫⁻ x, f x ∂(μ univ)⁻¹ • μ

notation3 "⨍⁻ " (...) ", " r:60:(scoped f => f) " ∂" μ:70 => laverage μ r

notation3 "⨍⁻ " (...) ", " r:60:(scoped f => laverage volume f) => r

notation3 "⨍⁻ " (...) " in " s ", " r:60:(scoped f => f) " ∂" μ:70 =>

  laverage (Measure.restrict μ s) r

notation3 (prettyPrint := false)

  "⨍⁻ " (...) " in " s ", " r:60:(scoped f => laverage Measure.restrict volume s f) => r
