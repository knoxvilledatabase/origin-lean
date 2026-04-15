/-
Extracted from Topology/MetricSpace/Closeds.lean
Genuine: 12 of 19 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty
compact subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `Closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `NonemptyCompacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

noncomputable section

open Set Function TopologicalSpace Filter Topology ENNReal

namespace Metric

variable {α : Type*} [PseudoEMetricSpace α]

theorem mem_hausdorffEntourage_of_hausdorffEDist_lt {s t : Set α} {δ : ℝ≥0∞}
    (h : hausdorffEDist s t < δ) : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 < δ} := by
  rw [hausdorffEDist, max_lt_iff] at h
  rw [hausdorffEntourage, Set.mem_setOf]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x ∈ s, infEDist x t < δ) :
      s ⊆ SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩

protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace (Set α) where
  edist s t := hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
        Filter.mem_iInf_of_mem ε <| Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
      with _ h using hδε.trans_le' <| hausdorffEDist_le_of_mem_hausdorffEntourage h

end Metric

namespace TopologicalSpace

open Metric

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {s : Set α}

namespace Closeds

-- INSTANCE (free from Core): instEMetricSpace

theorem continuous_infEDist :
    Continuous fun p : α × Closeds α => infEDist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s ≤ infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ ≤ infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc, hausdorffEDist_comm]
    _ ≤ infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

-- INSTANCE (free from Core): instCompleteSpace

theorem isometry_singleton : Isometry ({·} : α → Closeds α) :=
  fun _ _ => hausdorffEDist_singleton

theorem lipschitz_sup : LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

theorem lipschitz_prod : LipschitzWith 1 fun p : Closeds α × Closeds β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Closeds

namespace Compacts

-- INSTANCE (free from Core): instEMetricSpace

theorem isometry_toCloseds : Isometry (Compacts.toCloseds (α := α)) :=
  fun _ _ => rfl

theorem isometry_singleton : Isometry ({·} : α → Compacts α) :=
  fun _ _ => hausdorffEDist_singleton

theorem lipschitz_sup :
    LipschitzWith 1 fun p : Compacts α × Compacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

theorem lipschitz_prod :
    LipschitzWith 1 fun p : Compacts α × Compacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Compacts

namespace NonemptyCompacts

-- INSTANCE (free from Core): instEMetricSpace

theorem isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _) :=
  fun _ _ => rfl

theorem isometry_toCompacts : Isometry (NonemptyCompacts.toCompacts (α := α)) :=
  fun _ _ => rfl
