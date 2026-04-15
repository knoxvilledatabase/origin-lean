/-
Extracted from Analysis/Normed/Group/Completeness.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Completeness of normed groups

This file includes a completeness criterion for normed additive groups in terms of convergent
series.

## Main results

* `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`: A normed additive group is
  complete if any absolutely convergent series converges in the space.

## References

* [bergh_lofstrom_1976] `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` and
  `NormedAddCommGroup.summable_imp_tendsto_of_complete` correspond to the two directions of
  Lemma 2.2.1.

## Tags

CompleteSpace, CauchySeq
-/

open scoped Topology

open Filter Finset

section Metric

variable {α : Type*} [PseudoMetricSpace α]

lemma Metric.exists_subseq_summable_dist_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Summable fun i => dist (u (f (i + 1))) (u (f i)) := by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n => (1 / (2 : ℝ)) ^ n) (fun n => by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ summable_geometric_two
  exact fun n => le_of_lt <| hf₂ n (f (n + 1)) <| hf₁.monotone (Nat.le_add_right n 1)

end Metric

section Normed

variable {E : Type*} [NormedAddCommGroup E]

lemma NormedAddCommGroup.summable_imp_tendsto_of_complete [CompleteSpace E] (u : ℕ → E)
    (hu : Summable (‖u ·‖)) : ∃ a, Tendsto (fun n => ∑ i ∈ range n, u i) atTop (𝓝 a) := by
  refine cauchySeq_tendsto_of_complete <| cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

lemma NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace :
    (∀ u : ℕ → E, Summable (‖u ·‖) → ∃ a, Tendsto (fun n => ∑ i ∈ range n, u i) atTop (𝓝 a))
     ↔ CompleteSpace E :=
  ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu => summable_imp_tendsto_of_complete u hu⟩

end Normed
