/-
Extracted from Probability/Martingale/Centering.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process which is strongly adapted and integrable can be written as the
sum of a martingale and a predictable process. This result is also known as
**Doob's decomposition theorem**. From a process `f`, a filtration `ℱ` and a measure `μ`, we define
two processes `martingalePart f ℱ μ` and `predictablePart f ℱ μ`.

## Main definitions

* `MeasureTheory.predictablePart f ℱ μ`: a predictable process such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`
* `MeasureTheory.martingalePart f ℱ μ`: a martingale such that
  `f = predictablePart f ℱ μ + martingalePart f ℱ μ`

## Main statements

* `MeasureTheory.stronglyAdapted_predictablePart`: `(fun n => predictablePart f ℱ μ (n+1))`
  is strongly adapted.
  That is, `predictablePart` is predictable.
* `MeasureTheory.martingale_martingalePart`: `martingalePart f ℱ μ` is a martingale.

-/

open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {f : ℕ → Ω → E} {ℱ : Filtration ℕ m0}

noncomputable def predictablePart {m0 : MeasurableSpace Ω} (f : ℕ → Ω → E) (ℱ : Filtration ℕ m0)
    (μ : Measure Ω) : ℕ → Ω → E := fun n => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i]
