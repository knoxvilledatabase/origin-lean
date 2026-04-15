/-
Extracted from Analysis/Convex/Topology.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological properties of convex sets

We prove the following facts:

* `Convex.interior` : interior of a convex set is convex;
* `Convex.closure` : closure of a convex set is convex;
* `closedConvexHull_closure_eq_closedConvexHull` : the closed convex hull of the closure of a set is
  equal to the closed convex hull of the set;
* `Set.Finite.isCompact_convexHull` : convex hull of a finite set is compact;
* `Set.Finite.isClosed_convexHull` : convex hull of a finite set is closed.
-/

assert_not_exists Cardinal Norm

open Metric Bornology Set Pointwise Convex

variable {ι 𝕜 E : Type*}

namespace Real

variable {s : Set ℝ} {r ε : ℝ}

lemma closedBall_eq_segment (hε : 0 ≤ ε) : closedBall r ε = segment ℝ (r - ε) (r + ε) := by
  rw [closedBall_eq_Icc, segment_eq_Icc ((sub_le_self _ hε).trans <| le_add_of_nonneg_right hε)]

lemma ball_eq_openSegment (hε : 0 < ε) : ball r ε = openSegment ℝ (r - ε) (r + ε) := by
  rw [ball_eq_Ioo, openSegment_eq_Ioo ((sub_lt_self _ hε).trans <| lt_add_of_pos_right _ hε)]

theorem convex_iff_isPreconnected : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ordConnected.trans isPreconnected_iff_ordConnected.symm

end Real

alias ⟨_, IsPreconnected.convex⟩ := Real.convex_iff_isPreconnected

/-! ### Topological vector spaces -/

section TopologicalSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {x y : E}

theorem segment_subset_closure_openSegment : [x -[𝕜] y] ⊆ closure (openSegment 𝕜 x y) := by
  rw [segment_eq_image, openSegment_eq_image, ← closure_Ioo (zero_ne_one' 𝕜)]
  exact image_closure_subset_closure_image (by fun_prop)

end TopologicalSpace

section PseudoMetricSpace

variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
  [PseudoMetricSpace 𝕜] [OrderTopology 𝕜]
  [ProperSpace 𝕜] [CompactIccSpace 𝕜] [AddCommGroup E] [TopologicalSpace E] [T2Space E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
