/-
Extracted from Topology/MetricSpace/Bounded.lean
Genuine: 13 of 15 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
## Boundedness in (pseudo)-metric spaces

This file contains one definition, and various results on boundedness in pseudo-metric spaces.
* `Metric.diam s` : The `iSup` of the distances of members of `s`.
  Defined in terms of `ediam`, for better handling of the case when it should be infinite.

* `isBounded_iff_subset_closedBall`: a non-empty set is bounded if and only if
  it is included in some closed ball
* describing the cobounded filter, relating to the cocompact filter
* `IsCompact.isBounded`: compact sets are bounded
* `TotallyBounded.isBounded`: totally bounded sets are bounded
* `isCompact_iff_isClosed_bounded`, the **Heine–Borel theorem**:
  in a proper space, a set is compact if and only if it is closed and bounded.
* `cobounded_eq_cocompact`: in a proper space, cobounded and compact sets are the same
  diameter of a subset, and its relation to boundedness

## Tags

metric, pseudometric space, bounded, diameter, Heine-Borel theorem
-/

assert_not_exists Module.Basis

open Set Filter Bornology

open scoped ENNReal Uniformity Topology Pointwise

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section UniformSpace

variable [UniformSpace α] [Preorder α] [CompactIccSpace α]

lemma totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded

lemma totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  (totallyBounded_Icc a b).subset Ico_subset_Icc_self

lemma totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  (totallyBounded_Icc a b).subset Ioc_subset_Icc_self

lemma totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  (totallyBounded_Icc a b).subset Ioo_subset_Icc_self

end UniformSpace

namespace Metric

section Bounded

variable {x : α} {s t : Set α} {r : ℝ}

variable [PseudoMetricSpace α]

theorem isBounded_closedBall : IsBounded (closedBall x r) :=
  isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
    _ ≤ r + r := add_le_add hy hz⟩

theorem isBounded_ball : IsBounded (ball x r) :=
  isBounded_closedBall.subset ball_subset_closedBall

theorem isBounded_sphere : IsBounded (sphere x r) :=
  isBounded_closedBall.subset sphere_subset_closedBall

theorem isBounded_iff_subset_closedBall (c : α) : IsBounded s ↔ ∃ r, s ⊆ closedBall c r :=
  ⟨fun h ↦ (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx ↦ hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ ↦ isBounded_closedBall.subset hr⟩

theorem _root_.Bornology.IsBounded.subset_closedBall (h : IsBounded s) (c : α) :
    ∃ r, s ⊆ closedBall c r :=
  (isBounded_iff_subset_closedBall c).1 h

theorem _root_.Bornology.IsBounded.subset_ball (h : IsBounded s) (c : α) : ∃ r, s ⊆ ball c r :=
  (h.subset_ball_lt 0 c).imp fun _ ↦ And.right

theorem isBounded_iff_subset_ball (c : α) : IsBounded s ↔ ∃ r, s ⊆ ball c r :=
  ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ ↦ isBounded_ball.subset hr⟩

theorem isBounded_closure_of_isBounded (h : IsBounded s) : IsBounded (closure s) :=
  let ⟨C, h⟩ := isBounded_iff.1 h
  isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset <|
    map_mem_closure₂ continuous_dist ha hb h⟩

protected theorem _root_.Bornology.IsBounded.closure (h : IsBounded s) : IsBounded (closure s) :=
  isBounded_closure_of_isBounded h
