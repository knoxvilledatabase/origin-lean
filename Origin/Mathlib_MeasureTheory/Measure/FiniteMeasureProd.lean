/-
Extracted from MeasureTheory/Measure/FiniteMeasureProd.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Products of finite measures and probability measures

This file introduces binary products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.prod`: The product of two finite measures.
* `MeasureTheory.ProbabilityMeasure.prod`: The product of two probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_prod`: the product probability measure depends
continuously on the factors.

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section FiniteMeasure_product

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)
