/-
Extracted from MeasureTheory/OuterMeasure/Basic.lean
Genuine: 37 of 41 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Disjointed
import Mathlib.MeasureTheory.OuterMeasure.Defs

/-!
# Outer Measures

An outer measure is a function `μ : Set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/

noncomputable section

open Set Function Filter

open scoped NNReal Topology ENNReal

namespace MeasureTheory

section OuterMeasureClass

variable {α ι F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α]
  {μ : F} {s t : Set α}

@[simp]
theorem measure_empty : μ ∅ = 0 := OuterMeasureClass.measure_empty μ

@[mono, gcongr]
theorem measure_mono (h : s ⊆ t) : μ s ≤ μ t :=
  OuterMeasureClass.measure_mono μ h

theorem measure_mono_null (h : s ⊆ t) (ht : μ t = 0) : μ s = 0 :=
  eq_bot_mono (measure_mono h) ht

-- DISSOLVED: measure_pos_of_superset

theorem measure_iUnion_le [Countable ι] (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) := by
  refine rel_iSup_tsum μ measure_empty (· ≤ ·) (fun t ↦ ?_) _
  calc
    μ (⋃ i, t i) = μ (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ ≤ ∑' i, μ (disjointed t i) :=
      OuterMeasureClass.measure_iUnion_nat_le _ _ (disjoint_disjointed _)
    _ ≤ ∑' i, μ (t i) := by gcongr; apply disjointed_subset

theorem measure_biUnion_le {I : Set ι} (μ : F) (hI : I.Countable) (s : ι → Set α) :
    μ (⋃ i ∈ I, s i) ≤ ∑' i : I, μ (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le

theorem measure_biUnion_finset_le (I : Finset ι) (s : ι → Set α) :
    μ (⋃ i ∈ I, s i) ≤ ∑ i ∈ I, μ (s i) :=
  (measure_biUnion_le μ I.countable_toSet s).trans_eq <| I.tsum_subtype (μ <| s ·)

theorem measure_iUnion_fintype_le [Fintype ι] (μ : F) (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑ i, μ (s i) := by
  simpa using measure_biUnion_finset_le Finset.univ s

theorem measure_union_le (s t : Set α) : μ (s ∪ t) ≤ μ s + μ t := by
  simpa [union_eq_iUnion] using measure_iUnion_fintype_le μ (cond · s t)

lemma measure_univ_le_add_compl (s : Set α) : μ univ ≤ μ s + μ sᶜ :=
  s.union_compl_self ▸ measure_union_le s sᶜ

theorem measure_le_inter_add_diff (μ : F) (s t : Set α) : μ s ≤ μ (s ∩ t) + μ (s \ t) := by
  simpa using measure_union_le (s ∩ t) (s \ t)

theorem measure_diff_null (ht : μ t = 0) : μ (s \ t) = μ s :=
  (measure_mono diff_subset).antisymm <| calc
    μ s ≤ μ (s ∩ t) + μ (s \ t) := measure_le_inter_add_diff _ _ _
    _ ≤ μ t + μ (s \ t) := by gcongr; apply inter_subset_right
    _ = μ (s \ t) := by simp [ht]

theorem measure_biUnion_null_iff {I : Set ι} (hI : I.Countable) {s : ι → Set α} :
    μ (⋃ i ∈ I, s i) = 0 ↔ ∀ i ∈ I, μ (s i) = 0 := by
  refine ⟨fun h i hi ↦ measure_mono_null (subset_biUnion_of_mem hi) h, fun h ↦ ?_⟩
  have _ := hI.to_subtype
  simpa [h] using measure_iUnion_le (μ := μ) fun x : I ↦ s x

theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) :
    μ (⋃₀ S) = 0 ↔ ∀ s ∈ S, μ s = 0 := by
  rw [sUnion_eq_biUnion, measure_biUnion_null_iff hS]

@[simp]
theorem measure_iUnion_null_iff {ι : Sort*} [Countable ι] {s : ι → Set α} :
    μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 := by
  rw [← sUnion_range, measure_sUnion_null_iff (countable_range s), forall_mem_range]

alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff

@[simp]
theorem measure_union_null_iff : μ (s ∪ t) = 0 ↔ μ s = 0 ∧ μ t = 0 := by
  simp [union_eq_iUnion, and_comm]

theorem measure_union_null (hs : μ s = 0) (ht : μ t = 0) : μ (s ∪ t) = 0 := by simp [*]

lemma measure_null_iff_singleton (hs : s.Countable) : μ s = 0 ↔ ∀ x ∈ s, μ {x} = 0 := by
  rw [← measure_biUnion_null_iff hs, biUnion_of_singleton]

theorem measure_iUnion_of_tendsto_zero {ι} (μ : F) {s : ι → Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => μ ((⋃ n, s n) \ s k)) l (𝓝 0)) : μ (⋃ n, s n) = ⨆ n, μ (s n) := by
  refine le_antisymm ?_ <| iSup_le fun n ↦ measure_mono <| subset_iUnion _ _
  set S := ⋃ n, s n
  set M := ⨆ n, μ (s n)
  have A : ∀ k, μ S ≤ M + μ (S \ s k) := fun k ↦ calc
    μ S ≤ μ (S ∩ s k) + μ (S \ s k) := measure_le_inter_add_diff _ _ _
    _ ≤ μ (s k) + μ (S \ s k) := by gcongr; apply inter_subset_right
    _ ≤ M + μ (S \ s k) := by gcongr; exact le_iSup (μ ∘ s) k
  have B : Tendsto (fun k ↦ M + μ (S \ s k)) l (𝓝 M) := by simpa using tendsto_const_nhds.add h0
  exact ge_of_tendsto' B A

theorem measure_null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α]
    (s : Set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, μ u = 0) : μ s = 0 := by
  choose! u hxu hu₀ using hs
  choose t ht using TopologicalSpace.countable_cover_nhdsWithin hxu
  rcases ht with ⟨ts, t_count, ht⟩
  apply measure_mono_null ht
  exact (measure_biUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)

-- DISSOLVED: exists_mem_forall_mem_nhdsWithin_pos_measure

end OuterMeasureClass

namespace OuterMeasure

variable {α β : Type*} {m : OuterMeasure α}

theorem empty' (m : OuterMeasure α) : m ∅ = 0 := measure_empty

theorem mono' (m : OuterMeasure α) {s₁ s₂} (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ := by gcongr

theorem mono_null (m : OuterMeasure α) {s t} (h : s ⊆ t) (ht : m t = 0) : m s = 0 :=
  measure_mono_null h ht

-- DISSOLVED: pos_of_subset_ne_zero

protected theorem iUnion (m : OuterMeasure α) {β} [Countable β] (s : β → Set α) :
    m (⋃ i, s i) ≤ ∑' i, m (s i) :=
  measure_iUnion_le s

theorem biUnion_null_iff (m : OuterMeasure α) {s : Set β} (hs : s.Countable) {t : β → Set α} :
    m (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, m (t i) = 0 :=
  measure_biUnion_null_iff hs

theorem sUnion_null_iff (m : OuterMeasure α) {S : Set (Set α)} (hS : S.Countable) :
    m (⋃₀ S) = 0 ↔ ∀ s ∈ S, m s = 0 := measure_sUnion_null_iff hS

theorem iUnion_null_iff {ι : Sort*} [Countable ι] (m : OuterMeasure α) {s : ι → Set α} :
    m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 :=
  measure_iUnion_null_iff

alias ⟨_, iUnion_null⟩ := iUnion_null_iff

protected theorem iUnion_finset (m : OuterMeasure α) (s : β → Set α) (t : Finset β) :
    m (⋃ i ∈ t, s i) ≤ ∑ i ∈ t, m (s i) :=
  measure_biUnion_finset_le t s

protected theorem union (m : OuterMeasure α) (s₁ s₂ : Set α) : m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
  measure_union_le s₁ s₂

theorem null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α] (m : OuterMeasure α)
    (s : Set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, m u = 0) : m s = 0 :=
  measure_null_of_locally_null s hs

-- DISSOLVED: exists_mem_forall_mem_nhds_within_pos

theorem iUnion_of_tendsto_zero {ι} (m : OuterMeasure α) {s : ι → Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => m ((⋃ n, s n) \ s k)) l (𝓝 0)) : m (⋃ n, s n) = ⨆ n, m (s n) :=
  measure_iUnion_of_tendsto_zero m l h0

theorem iUnion_nat_of_monotone_of_tsum_ne_top (m : OuterMeasure α) {s : ℕ → Set α}
    (h_mono : ∀ n, s n ⊆ s (n + 1)) (h0 : (∑' k, m (s (k + 1) \ s k)) ≠ ∞) :
    m (⋃ n, s n) = ⨆ n, m (s n) := by
  classical
  refine measure_iUnion_of_tendsto_zero m atTop ?_
  refine tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => ?_
  refine (m.mono ?_).trans (measure_iUnion_le _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone_nat_of_le_succ (Set α) _ _ h_mono
  simp only [diff_subset_iff, iUnion_subset_iff]
  intro i x hx
  have : ∃i, x ∈ s i := by exists i
  rcases Nat.findX this with ⟨j, hj, hlt⟩
  clear hx i
  rcases le_or_lt j n with hjn | hnj
  · exact Or.inl (h' hjn hj)
  have : j - (n + 1) + n + 1 = j := by omega
  refine Or.inr (mem_iUnion.2 ⟨j - (n + 1), ?_, hlt _ ?_⟩)
  · rwa [this]
  · rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, this]

theorem le_inter_add_diff {m : OuterMeasure α} {t : Set α} (s : Set α) :
    m t ≤ m (t ∩ s) + m (t \ s) :=
  measure_le_inter_add_diff m t s

theorem diff_null (m : OuterMeasure α) (s : Set α) {t : Set α} (ht : m t = 0) : m (s \ t) = m s :=
  measure_diff_null ht

theorem union_null (m : OuterMeasure α) {s₁ s₂ : Set α} (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) :
    m (s₁ ∪ s₂) = 0 :=
  measure_union_null h₁ h₂

theorem coe_fn_injective : Injective fun (μ : OuterMeasure α) (s : Set α) => μ s :=
  DFunLike.coe_injective

@[ext]
theorem ext {μ₁ μ₂ : OuterMeasure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  DFunLike.ext _ _ h

theorem ext_nonempty {μ₁ μ₂ : OuterMeasure α} (h : ∀ s : Set α, s.Nonempty → μ₁ s = μ₂ s) :
    μ₁ = μ₂ :=
  ext fun s => s.eq_empty_or_nonempty.elim (fun he => by simp [he]) (h s)

end OuterMeasure

end MeasureTheory
