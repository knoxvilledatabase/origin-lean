/-
Extracted from MeasureTheory/Measure/EverywherePos.lean
Genuine: 15 of 17 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Everywhere positive sets in measure spaces

A set `s` in a topological space with a measure `μ` is *everywhere positive* (also called
*self-supporting*) if any neighborhood `n` of any point of `s` satisfies `μ (s ∩ n) > 0`.

## Main definitions and results

* `μ.IsEverywherePos s` registers that, for any point in `s`, all its neighborhoods have positive
  measure inside `s`.
* `μ.everywherePosSubset s` is the subset of `s` made of those points all of whose neighborhoods
  have positive measure inside `s`.
* `everywherePosSubset_ae_eq` shows that `s` and `μ.everywherePosSubset s` coincide almost
  everywhere if `μ` is inner regular and `s` is measurable.
* `isEverywherePos_everywherePosSubset` shows that `μ.everywherePosSubset s` satisfies the property
  `μ.IsEverywherePos` if `μ` is inner regular and `s` is measurable.

The latter two statements have also versions when `μ` is inner regular for finite measure sets,
assuming additionally that `s` has finite measure.

* `IsEverywherePos.IsGδ` proves that an everywhere positive compact closed set is a Gδ set,
  in a topological group with a left-invariant measure. This is a nontrivial statement, used
  crucially in the study of the uniqueness of Haar measures.
* `innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top`: for a Haar measure, any
  finite measure set can be approximated from inside by level sets of continuous
  compactly supported functions. This property is also known as completion-regularity of Haar
  measures.
-/

open scoped Topology ENNReal NNReal

open Set Filter

namespace MeasureTheory.Measure

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

def IsEverywherePos (μ : Measure α) (s : Set α) : Prop :=
  ∀ x ∈ s, ∀ n ∈ 𝓝[s] x, 0 < μ n

def everywherePosSubset (μ : Measure α) (s : Set α) : Set α :=
  {x | x ∈ s ∧ ∀ n ∈ 𝓝[s] x, 0 < μ n}

lemma everywherePosSubset_subset (μ : Measure α) (s : Set α) : μ.everywherePosSubset s ⊆ s :=
  fun _x hx ↦ hx.1

lemma exists_isOpen_everywherePosSubset_eq_diff (μ : Measure α) (s : Set α) :
    ∃ u, IsOpen u ∧ μ.everywherePosSubset s = s \ u := by
  refine ⟨{x | ∃ n ∈ 𝓝[s] x, μ n = 0}, ?_, by ext x; simp [everywherePosSubset, pos_iff_ne_zero]⟩
  rw [isOpen_iff_mem_nhds]
  intro x ⟨n, ns, hx⟩
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ns with ⟨v, vx, hv⟩
  rcases mem_nhds_iff.1 vx with ⟨w, wv, w_open, xw⟩
  have A : w ⊆ {x | ∃ n ∈ 𝓝[s] x, μ n = 0} := by
    intro y yw
    refine ⟨s ∩ w, inter_mem_nhdsWithin _ (w_open.mem_nhds yw), measure_mono_null ?_ hx⟩
    rw [inter_comm]
    exact (inter_subset_inter_left _ wv).trans hv
  have B : w ∈ 𝓝 x := w_open.mem_nhds xw
  exact mem_of_superset B A

variable {μ ν : Measure α} {s k : Set α}

protected lemma _root_.MeasurableSet.everywherePosSubset [OpensMeasurableSpace α]
    (hs : MeasurableSet s) :
    MeasurableSet (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open.measurableSet

protected lemma _root_.IsClosed.everywherePosSubset (hs : IsClosed s) :
    IsClosed (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.sdiff u_open

protected lemma _root_.IsCompact.everywherePosSubset (hs : IsCompact s) :
    IsCompact (μ.everywherePosSubset s) := by
  rcases exists_isOpen_everywherePosSubset_eq_diff μ s with ⟨u, u_open, hu⟩
  rw [hu]
  exact hs.diff u_open

lemma measure_eq_zero_of_subset_diff_everywherePosSubset
    (hk : IsCompact k) (h'k : k ⊆ s \ μ.everywherePosSubset s) : μ k = 0 := by
  apply hk.induction_on (p := fun t ↦ μ t = 0)
  · exact measure_empty
  · exact fun s t hst ht ↦ measure_mono_null hst ht
  · exact fun s t hs ht ↦ measure_union_null hs ht
  · intro x hx
    obtain ⟨u, ux, hu⟩ : ∃ u ∈ 𝓝[s] x, μ u = 0 := by
      simpa [everywherePosSubset, (h'k hx).1] using (h'k hx).2
    exact ⟨u, nhdsWithin_mono x (h'k.trans diff_subset) ux, hu⟩

lemma everywherePosSubset_ae_eq [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  simp only [ae_eq_set, diff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact, ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_diff_everywherePosSubset h'k hk

lemma everywherePosSubset_ae_eq_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.everywherePosSubset s =ᵐ[μ] s := by
  have A : μ (s \ μ.everywherePosSubset s) ≠ ∞ :=
    ((measure_mono diff_subset).trans_lt h's.lt_top).ne
  simp only [ae_eq_set, diff_eq_empty.mpr (everywherePosSubset_subset μ s), measure_empty,
    true_and, (hs.diff hs.everywherePosSubset).measure_eq_iSup_isCompact_of_ne_top A,
    ENNReal.iSup_eq_zero]
  intro k hk h'k
  exact measure_eq_zero_of_subset_diff_everywherePosSubset h'k hk

lemma isEverywherePos_everywherePosSubset
    [OpensMeasurableSpace α] [InnerRegular μ] (hs : MeasurableSet s) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq hs)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

lemma isEverywherePos_everywherePosSubset_of_measure_ne_top
    [OpensMeasurableSpace α] [InnerRegularCompactLTTop μ] (hs : MeasurableSet s) (h's : μ s ≠ ∞) :
    μ.IsEverywherePos (μ.everywherePosSubset s) := by
  intro x hx n hn
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hn with ⟨u, u_mem, hu⟩
  have A : 0 < μ (u ∩ s) := by
    have : u ∩ s ∈ 𝓝[s] x := by rw [inter_comm]; exact inter_mem_nhdsWithin s u_mem
    exact hx.2 _ this
  have B : (u ∩ μ.everywherePosSubset s : Set α) =ᵐ[μ] (u ∩ s : Set α) :=
    ae_eq_set_inter (ae_eq_refl _) (everywherePosSubset_ae_eq_of_measure_ne_top hs h's)
  rw [← B.measure_eq] at A
  exact A.trans_le (measure_mono hu)

-- DISSOLVED: IsEverywherePos.smul_measure

-- DISSOLVED: IsEverywherePos.smul_measure_nnreal

lemma IsEverywherePos.of_forall_exists_nhds_eq (hs : IsEverywherePos μ s)
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) : IsEverywherePos ν s := by
  intro x hx n hn
  rcases h x hx with ⟨t, t_mem, ht⟩
  grw [← inter_subset_left (s := n)]
  rw [ht (n ∩ t) inter_subset_right]
  exact hs x hx _ (inter_mem hn (mem_nhdsWithin_of_mem_nhds t_mem))

lemma isEverywherePos_iff_of_forall_exists_nhds_eq (h : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∀ u ⊆ t, ν u = μ u) :
    IsEverywherePos ν s ↔ IsEverywherePos μ s := by
  refine ⟨fun H ↦ H.of_forall_exists_nhds_eq ?_, fun H ↦ H.of_forall_exists_nhds_eq h⟩
  intro x hx
  rcases h x hx with ⟨t, ht, h't⟩
  exact ⟨t, ht, fun u hu ↦ (h't u hu).symm⟩

lemma _root_.IsOpen.isEverywherePos [IsOpenPosMeasure μ] (hs : IsOpen s) : IsEverywherePos μ s := by
  intro x xs n hn
  rcases mem_nhdsWithin.1 hn with ⟨u, u_open, xu, hu⟩
  apply lt_of_lt_of_le _ (measure_mono hu)
  exact (u_open.inter hs).measure_pos μ ⟨x, ⟨xu, xs⟩⟩

section IsTopologicalGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [IsMulLeftInvariant μ] [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]

open Pointwise
