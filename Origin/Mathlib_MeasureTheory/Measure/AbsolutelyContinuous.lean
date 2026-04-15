/-
Extracted from MeasureTheory/Measure/AbsolutelyContinuous.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolute Continuity of Measures

We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
if `ν(A) = 0` implies that `μ(A) = 0`. We denote that by `μ ≪ ν`.

It is equivalent to an inequality of the almost everywhere filters of the measures:
`μ ≪ ν ↔ ae μ ≤ ae ν`.

## Main definitions

* `MeasureTheory.Measure.AbsolutelyContinuous μ ν`: `μ` is absolutely continuous with respect to `ν`

## Main statements

* `ae_le_iff_absolutelyContinuous`: `ae μ ≤ ae ν ↔ μ ≪ ν`

## Notation

* `μ ≪ ν`: `MeasureTheory.Measure.AbsolutelyContinuous μ ν`. That is: `μ` is absolutely continuous
  with respect to `ν`

-/

variable {α β δ ι R : Type*}

namespace MeasureTheory

open Set ENNReal NNReal

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ μ₁ μ₂ μ₃ ν ν' : Measure α} {s t : Set α}

namespace Measure

def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0
