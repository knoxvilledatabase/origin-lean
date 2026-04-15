/-
Extracted from Topology/Algebra/Group/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological groups

This file defines the following typeclasses:

* `IsTopologicalGroup`, `IsTopologicalAddGroup`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `ContinuousSub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `ContinuousSub` from `IsTopologicalGroup` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `Homeomorph` versions of several `Equiv`s: `Homeomorph.mulLeft`,
`Homeomorph.mulRight`, `Homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}

lemma Set.isClosed_centralizer {M : Type*} (s : Set M) [Mul M] [TopologicalSpace M]
    [SeparatelyContinuousMul M] [T2Space M] : IsClosed (centralizer s) := by
  rw [centralizer, setOf_forall]
  refine isClosed_sInter ?_
  rintro - ⟨m, ht, rfl⟩
  refine isClosed_imp (by simp) <| isClosed_eq ?_ ?_
  all_goals fun_prop

section ContinuousMulGroup

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/

variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]
