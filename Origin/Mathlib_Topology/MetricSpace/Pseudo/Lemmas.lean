/-
Extracted from Topology/MetricSpace/Pseudo/Lemmas.lean
Genuine: 15 of 16 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Extra lemmas about pseudo-metric spaces
-/

open Bornology Filter Metric Set

open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

lemma Real.singleton_eq_inter_Icc (b : ℝ) : {b} = ⋂ (r > 0), Icc (b - r) (b + r) := by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

lemma squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

lemma eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε

lemma tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets :=
  tendsto_smallSets_iff.2 fun _ ↦ eventually_closedBall_subset

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

lemma isClosed_ball : IsClosed (closedBall x ε) :=
  isClosed_le (continuous_id.dist continuous_const) continuous_const

lemma isClosed_sphere : IsClosed (sphere x ε) :=
  isClosed_eq (continuous_id.dist continuous_const) continuous_const

@[simp]
lemma closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_ball.closure_eq

@[simp]
lemma closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq

lemma closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_ball

lemma frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (continuous_id.dist continuous_const) continuous_const

lemma frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (continuous_id.dist continuous_const) continuous_const

lemma closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_ball)

lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_ball hr

lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∃ r, 0 < r ∧ IsCompact (closedBall x r) := by
  have : ∀ᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists

end Metric
