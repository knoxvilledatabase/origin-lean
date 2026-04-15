/-
Extracted from Dynamics/FixedPoints/Topology.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological properties of fixed points

Currently this file contains two lemmas:

- `isFixedPt_of_tendsto_iterate`: if `f^n(x) → y` and `f` is continuous at `y`, then `f y = y`;
- `isClosed_fixedPoints`: the set of fixed points of a continuous map is a closed set.

## TODO

fixed points, iterates
-/

variable {α : Type*} [TopologicalSpace α] [T2Space α] {f : α → α}

open Function Filter

open Topology

theorem isFixedPt_of_tendsto_iterate {x y : α} (hy : Tendsto (fun n => f^[n] x) atTop (𝓝 y))
    (hf : ContinuousAt f y) : IsFixedPt f y := by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).1 ?_) hy
  simp only [iterate_succ' f]
  exact hf.tendsto.comp hy

theorem isClosed_fixedPoints (hf : Continuous f) : IsClosed (fixedPoints f) :=
  isClosed_eq hf continuous_id
