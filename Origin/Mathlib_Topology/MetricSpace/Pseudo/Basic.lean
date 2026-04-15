/-
Extracted from Topology/MetricSpace/Pseudo/Basic.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## Pseudo-metric spaces

Further results about pseudo-metric spaces.

-/

open Set Filter TopologicalSpace Bornology

open scoped ENNReal NNReal Uniformity Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*}

variable [PseudoMetricSpace α]

theorem dist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, dist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, dist_self]
  | succ n hle ihn =>
    calc
      dist (f m) (f (n + 1)) ≤ dist (f m) (f n) + dist (f n) (f (n + 1)) := dist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

theorem dist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_dist f (Nat.zero_le n)

theorem dist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ}
    (hd : ∀ {k}, m ≤ k → k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (dist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

theorem dist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ}
    (hd : ∀ {k}, k < n → dist (f k) (f (k + 1)) ≤ d k) :
    dist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ dist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd

namespace Metric

nonrec theorem isUniformInducing_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_dist.comap _).le_basis_iff uniformity_basis_dist).trans <| by
      simp only [subset_def, Prod.forall, gt_iff_lt, preimage_setOf_eq, Prod.map_apply, mem_setOf]

nonrec theorem isUniformEmbedding_iff [PseudoMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff, and_comm, isUniformInducing_iff]

theorem controlled_of_isUniformInducing [PseudoMetricSpace β] {f : α → β}
    (h : IsUniformInducing f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, dist a b < δ → dist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩
