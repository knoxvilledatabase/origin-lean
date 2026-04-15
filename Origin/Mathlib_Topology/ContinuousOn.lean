/-
Extracted from Topology/ContinuousOn.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Neighborhoods and continuity relative to a subset

This file develops API on the relative versions

* `ContinuousOn`        of `Continuous`
* `ContinuousWithinAt`  of `ContinuousAt`

related to continuity, which are defined in previous definition files.
Their basic properties studied in this file include the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

-/

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ] {f g : α → β} {s s' s₁ t : Set α} {x : α}

/-!
## `ContinuousWithinAt`
-/

theorem continuousWithinAt_univ (f : α → β) (x : α) :
    ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt, ContinuousWithinAt, nhdsWithin_univ]
