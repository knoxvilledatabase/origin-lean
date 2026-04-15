/-
Extracted from MeasureTheory/Integral/IntegrableOn.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Functions integrable on a set and at a filter

We define `IntegrableOn f s μ := Integrable f (μ.restrict s)` and prove theorems like
`integrableOn_union : IntegrableOn f (s ∪ t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ`.

Next we define a predicate `IntegrableAtFilter (f : α → E) (l : Filter α) (μ : Measure α)`
saying that `f` is integrable at some set `s ∈ l` and prove that a measurable function is integrable
at `l` with respect to `μ` provided that `f` is bounded above at `l ⊓ ae μ` and `μ` is finite
at `l`.

-/

noncomputable section

open Set Filter TopologicalSpace MeasureTheory Function

open scoped Topology Interval Filter ENNReal MeasureTheory

variable {α β ε ε' E F : Type*} {mα : MeasurableSpace α}

variable [TopologicalSpace β] [ENorm ε] [TopologicalSpace ε]
  {l l' : Filter α} {f g : α → β} {μ ν : Measure α}

def StronglyMeasurableAtFilter (f : α → β) (l : Filter α) (μ : Measure α := by volume_tac) :=
  ∃ s ∈ l, AEStronglyMeasurable f (μ.restrict s)
