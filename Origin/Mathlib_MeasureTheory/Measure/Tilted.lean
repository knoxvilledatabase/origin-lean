/-
Extracted from MeasureTheory/Measure/Tilted.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Exponentially tilted measures

The exponential tilting of a measure `μ` on `α` by a function `f : α → ℝ` is the measure with
density `x ↦ exp (f x) / ∫ y, exp (f y) ∂μ` with respect to `μ`. This is sometimes also called
the Esscher transform.

The definition is mostly used for `f` linear, in which case the exponentially tilted measure belongs
to the natural exponential family of the base measure. Exponentially tilted measures for general `f`
can be used for example to establish variational expressions for the Kullback-Leibler divergence.

## Main definitions

* `Measure.tilted μ f`: exponential tilting of `μ` by `f`, equal to
  `μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))`.

-/

open Real

open scoped ENNReal NNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

noncomputable

def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α :=
  μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))
