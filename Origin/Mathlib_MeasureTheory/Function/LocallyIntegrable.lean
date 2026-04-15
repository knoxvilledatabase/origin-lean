/-
Extracted from MeasureTheory/Function/LocallyIntegrable.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally integrable functions

A function is called *locally integrable* (`MeasureTheory.LocallyIntegrable`) if it is integrable
on a neighborhood of every point. More generally, it is *locally integrable on `s`* if it is
locally integrable on a neighbourhood within `s` of any point of `s`.

This file contains properties of locally integrable functions, and integrability results
on compact sets.

## Main statements

* `Continuous.locallyIntegrable`: A continuous function is locally integrable.
* `ContinuousOn.locallyIntegrableOn`: A function which is continuous on `s` is locally
  integrable on `s`.
-/

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Bornology Filter

open scoped Topology Interval ENNReal

variable {X Y ε ε' ε'' E F R : Type*} [MeasurableSpace X] [TopologicalSpace X]

variable [MeasurableSpace Y] [TopologicalSpace Y]

variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : X → ε} {μ ν : Measure X} {s : Set X}

namespace MeasureTheory

section LocallyIntegrableOn

def LocallyIntegrableOn (f : X → ε) (s : Set X) (μ : Measure X := by volume_tac) : Prop :=
  ∀ x : X, x ∈ s → IntegrableAtFilter f (𝓝[s] x) μ
