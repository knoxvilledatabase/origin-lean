/-
Extracted from Topology/MetricSpace/ShrinkingLemma.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.ShrinkingLemma

/-!
# Shrinking lemma in a proper metric space

In this file we prove a few versions of the shrinking lemma for coverings by balls in a proper
(pseudo) metric space.

## Tags

shrinking lemma, metric space
-/

universe u v

open Set Metric

open Topology

variable {α : Type u} {ι : Type v} [MetricSpace α] [ProperSpace α] {c : ι → α}

variable {s : Set α}

theorem exists_subset_iUnion_ball_radius_lt {r : ι → ℝ} (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i < r i := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_lt_subset_ball (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono <| hsub, hlt⟩

theorem exists_iUnion_ball_eq_radius_lt {r : ι → ℝ} (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite)
    (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i < r i :=
  let ⟨r', hU, hv⟩ := exists_subset_iUnion_ball_radius_lt isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

theorem exists_subset_iUnion_ball_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hs : IsClosed s)
    (uf : ∀ x ∈ s, { i | x ∈ ball (c i) (r i) }.Finite) (us : s ⊆ ⋃ i, ball (c i) (r i)) :
    ∃ r' : ι → ℝ, (s ⊆ ⋃ i, ball (c i) (r' i)) ∧ ∀ i, r' i ∈ Ioo 0 (r i) := by
  rcases exists_subset_iUnion_closed_subset hs (fun i => @isOpen_ball _ _ (c i) (r i)) uf us with
    ⟨v, hsv, hvc, hcv⟩
  have := fun i => exists_pos_lt_subset_ball (hr i) (hvc i) (hcv i)
  choose r' hlt hsub using this
  exact ⟨r', hsv.trans <| iUnion_mono hsub, hlt⟩

theorem exists_iUnion_ball_eq_radius_pos_lt {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (uf : ∀ x, { i | x ∈ ball (c i) (r i) }.Finite) (uU : ⋃ i, ball (c i) (r i) = univ) :
    ∃ r' : ι → ℝ, ⋃ i, ball (c i) (r' i) = univ ∧ ∀ i, r' i ∈ Ioo 0 (r i) :=
  let ⟨r', hU, hv⟩ :=
    exists_subset_iUnion_ball_radius_pos_lt hr isClosed_univ (fun x _ => uf x) uU.ge
  ⟨r', univ_subset_iff.1 hU, hv⟩

theorem exists_locallyFinite_subset_iUnion_ball_radius_lt (hs : IsClosed s) {R : α → ℝ}
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, c i ∈ s ∧ 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ s ⊆ ⋃ i, ball (c i) (r i) := by
  have : ∀ x ∈ s, (𝓝 x).HasBasis (fun r : ℝ => 0 < r ∧ r < R x) fun r => ball x r := fun x hx =>
    nhds_basis_uniformity (uniformity_basis_dist_lt (hR x hx))
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs this with
    ⟨ι, c, r', hr', hsub', hfin⟩
  rcases exists_subset_iUnion_ball_radius_pos_lt (fun i => (hr' i).2.1) hs
      (fun x _ => hfin.point_finite x) hsub' with
    ⟨r, hsub, hlt⟩
  exact ⟨ι, c, r, r', fun i => ⟨(hr' i).1, (hlt i).1, (hlt i).2, (hr' i).2.2⟩, hfin, hsub⟩

theorem exists_locallyFinite_iUnion_eq_ball_radius_lt {R : α → ℝ} (hR : ∀ x, 0 < R x) :
    ∃ (ι : Type u) (c : ι → α) (r r' : ι → ℝ),
      (∀ i, 0 < r i ∧ r i < r' i ∧ r' i < R (c i)) ∧
        (LocallyFinite fun i => ball (c i) (r' i)) ∧ ⋃ i, ball (c i) (r i) = univ :=
  let ⟨ι, c, r, r', hlt, hfin, hsub⟩ :=
    exists_locallyFinite_subset_iUnion_ball_radius_lt isClosed_univ fun x _ => hR x
  ⟨ι, c, r, r', fun i => (hlt i).2, hfin, univ_subset_iff.1 hsub⟩
