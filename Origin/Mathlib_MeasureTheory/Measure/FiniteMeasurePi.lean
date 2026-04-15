/-
Extracted from MeasureTheory/Measure/FiniteMeasurePi.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Products of finite measures and probability measures

This file introduces finite products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.pi`: The product of finitely many finite measures.
* `MeasureTheory.ProbabilityMeasure.pi`: The product of finitely many probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_pi`: the product probability measure depends
continuously on the factors.

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)]

namespace FiniteMeasure

noncomputable def pi (μ : Π i, FiniteMeasure (α i)) : FiniteMeasure (Π i, α i) :=
  ⟨Measure.pi (fun i ↦ μ i), inferInstance⟩

variable (μ : Π i, FiniteMeasure (α i))
