/-
Extracted from Topology/EMetricSpace/Basic.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extended metric spaces

Further results about extended metric spaces.
-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, edist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ => hd

namespace EMetric

theorem isUniformInducing_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans <| by
      simp only [subset_def, Prod.forall]; rfl

nonrec theorem isUniformEmbedding_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  (isUniformEmbedding_iff _).trans <| and_comm.trans <| Iff.rfl.and isUniformInducing_iff

theorem controlled_of_isUniformInducing [PseudoEMetricSpace β] {f : α → β}
    (h : IsUniformInducing f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩
