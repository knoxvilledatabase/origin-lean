/-
Extracted from Topology/MetricSpace/Pseudo/Lemmas.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Extra lemmas about pseudo-metric spaces
-/

open Bornology Filter Metric Set

open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

-- INSTANCE (free from Core): :

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

lemma eventually_ball_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) : ∀ᶠ r in 𝓝 (0 : ℝ), ball x r ⊆ u :=
  (eventually_closedBall_subset hu).mono fun _r hr ↦ ball_subset_closedBall.trans hr

namespace Metric

variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

lemma isClosed_closedBall : IsClosed (closedBall x ε) := isClosed_le (by fun_prop) continuous_const

lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const
