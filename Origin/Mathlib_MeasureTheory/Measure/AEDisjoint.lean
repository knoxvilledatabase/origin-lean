/-
Extracted from MeasureTheory/Measure/AEDisjoint.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Almost everywhere disjoint sets

We say that sets `s` and `t` are `μ`-a.e. disjoint (see `MeasureTheory.AEDisjoint`) if their
intersection has measure zero. This assumption can be used instead of `Disjoint` in most theorems in
measure theory.
-/

open Set Function

namespace MeasureTheory

variable {ι α : Type*} {m : MeasurableSpace α} (μ : Measure α)

def AEDisjoint (s t : Set α) :=
  μ (s ∩ t) = 0

variable {μ} {s t u v : Set α}

theorem exists_null_pairwise_disjoint_diff [Countable ι] {s : ι → Set α}
    (hd : Pairwise (AEDisjoint μ on s)) : ∃ t : ι → Set α, (∀ i, MeasurableSet (t i)) ∧
    (∀ i, μ (t i) = 0) ∧ Pairwise (Disjoint on fun i => s i \ t i) := by
  refine ⟨fun i => toMeasurable μ (s i ∩ ⋃ j ∈ ({i}ᶜ : Set ι), s j), fun i =>
    measurableSet_toMeasurable _ _, fun i => ?_, ?_⟩
  · simp only [measure_toMeasurable, inter_iUnion]
    exact (measure_biUnion_null_iff <| to_countable _).2 fun j hj => hd (Ne.symm hj)
  · simp only [Pairwise, disjoint_left, onFun, mem_diff, not_and, and_imp, Classical.not_not]
    intro i j hne x hi hU hj
    replace hU : x ∉ s i ∩ iUnion fun j ↦ iUnion fun _ ↦ s j :=
      fun h ↦ hU (subset_toMeasurable _ _ h)
    simp only [mem_inter_iff, mem_iUnion, not_and, not_exists] at hU
    exact (hU hi j hne.symm hj).elim

namespace AEDisjoint
