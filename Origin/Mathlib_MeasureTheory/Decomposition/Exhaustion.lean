/-
Extracted from MeasureTheory/Decomposition/Exhaustion.lean
Genuine: 21 | Conflates: 0 | Dissolved: 3 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.MeasureTheory.Measure.Typeclasses

/-!
# Method of exhaustion

If `μ, ν` are two measures with `ν` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT ν` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ`, either `ν t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `ν` is not s-finite), we define
  `μ.sigmaFiniteSetWRT ν = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `ν`, for all sets `s`
  in `(sigmaFiniteSetWRT μ ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ ν)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ ν` and `ν` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

open Classical in

def Measure.sigmaFiniteSetWRT (μ ν : Measure α) : Set α :=
  if h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (∀ t, t ⊆ sᶜ → ν t ≠ 0 → μ t = ∞)
  then h.choose
  else ∅

@[measurability]
lemma measurableSet_sigmaFiniteSetWRT :
    MeasurableSet (μ.sigmaFiniteSetWRT ν) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.1
  · exact MeasurableSet.empty

instance : SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT ν)) := by
  rw [Measure.sigmaFiniteSetWRT]
  split_ifs with h
  · exact h.choose_spec.2.1
  · rw [Measure.restrict_empty]
    infer_instance

section IsFiniteMeasure

/-! We prove that the condition in the definition of `sigmaFiniteSetWRT` is true for finite
measures. Since every s-finite measure is absolutely continuous with respect to a finite measure,
the condition will then also be true for s-finite measures. -/

lemma exists_isSigmaFiniteSet_measure_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ∃ t, MeasurableSet t ∧ SigmaFinite (μ.restrict t)
      ∧ (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n ≤ ν t := by
  by_cases hC_lt : 1/n < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s
  · have h_lt_top : ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s < ∞ := by
      refine (?_ : ⨆ (s) (_ : MeasurableSet s)
        (_ : SigmaFinite (μ.restrict s)), ν s ≤ ν Set.univ).trans_lt (measure_lt_top _ _)
      refine iSup_le (fun s ↦ ?_)
      exact iSup_le (fun _ ↦ iSup_le (fun _ ↦ measure_mono (Set.subset_univ s)))
    obtain ⟨t, ht⟩ := exists_lt_of_lt_ciSup
      (ENNReal.sub_lt_self h_lt_top.ne (ne_zero_of_lt hC_lt) (by simp) :
          (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n
        < ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)
    have ht_meas : MeasurableSet t := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    have ht_mem : SigmaFinite (μ.restrict t) := by
      by_contra h_not_mem
      simp only [h_not_mem] at ht
      simp at ht
    refine ⟨t, ht_meas, ht_mem, ?_⟩
    simp only [ht_meas, ht_mem, iSup_true] at ht
    exact ht.le
  · refine ⟨∅, MeasurableSet.empty, by rw [Measure.restrict_empty]; infer_instance, ?_⟩
    rw [tsub_eq_zero_of_le (not_lt.mp hC_lt)]
    exact zero_le'

def Measure.sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) : Set α :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose

lemma measurableSet_sigmaFiniteSetGE [IsFiniteMeasure ν] (n : ℕ) :
    MeasurableSet (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.1

lemma sigmaFinite_restrict_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetGE ν n)) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.1

lemma measure_sigmaFiniteSetGE_le (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    ν (μ.sigmaFiniteSetGE ν n)
      ≤ ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  refine (le_iSup (f := fun s ↦ _)
    (sigmaFinite_restrict_sigmaFiniteSetGE μ ν n)).trans ?_
  exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetGE ν n)
    (measurableSet_sigmaFiniteSetGE n)

lemma measure_sigmaFiniteSetGE_ge (μ ν : Measure α) [IsFiniteMeasure ν] (n : ℕ) :
    (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s) - 1/n
      ≤ ν (μ.sigmaFiniteSetGE ν n) :=
  (exists_isSigmaFiniteSet_measure_ge μ ν n).choose_spec.2.2

lemma tendsto_measure_sigmaFiniteSetGE (μ ν : Measure α) [IsFiniteMeasure ν] :
    Tendsto (fun n ↦ ν (μ.sigmaFiniteSetGE ν n)) atTop
      (𝓝 (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_
    tendsto_const_nhds (measure_sigmaFiniteSetGE_ge μ ν) (measure_sigmaFiniteSetGE_le μ ν)
  nth_rewrite 2 [← tsub_zero (⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s)]
  refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (Or.inr ENNReal.zero_ne_top)
  simp only [one_div]
  exact ENNReal.tendsto_inv_nat_nhds_zero

def Measure.sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] : Set α :=
  ⋃ n, μ.sigmaFiniteSetGE ν n

lemma measurableSet_sigmaFiniteSetWRT' [IsFiniteMeasure ν] :
    MeasurableSet (μ.sigmaFiniteSetWRT' ν) :=
  MeasurableSet.iUnion measurableSet_sigmaFiniteSetGE

lemma sigmaFinite_restrict_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    SigmaFinite (μ.restrict (μ.sigmaFiniteSetWRT' ν)) := by
  have := sigmaFinite_restrict_sigmaFiniteSetGE μ ν
  let f : ℕ × ℕ → Set α := fun p : ℕ × ℕ ↦ (μ.sigmaFiniteSetWRT' ν)ᶜ
    ∪ (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν p.1)) p.2 ∩ (μ.sigmaFiniteSetGE ν p.1))
  suffices (μ.restrict (μ.sigmaFiniteSetWRT' ν)).FiniteSpanningSetsIn (Set.range f) from
    this.sigmaFinite
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  refine ⟨fun n ↦ f (e n), fun _ ↦ by simp, fun n ↦ ?_, ?_⟩
  · simp only [Nat.pairEquiv_symm_apply, gt_iff_lt, measure_union_lt_top_iff, f, e]
    rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT', Set.compl_inter_self,
      Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT']
    simp only [measure_empty, ENNReal.zero_lt_top, true_and]
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
    rw [← Measure.restrict_apply' (measurableSet_sigmaFiniteSetGE _)]
    exact measure_spanningSets_lt_top _ _
  · simp only [Nat.pairEquiv_symm_apply, f, e]
    rw [← Set.union_iUnion]
    suffices ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1) = μ.sigmaFiniteSetWRT' ν by
      rw [this, Set.compl_union_self]
    calc ⋃ n, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν (Nat.unpair n).1)) n.unpair.2
        ∩ μ.sigmaFiniteSetGE ν n.unpair.1)
      = ⋃ n, ⋃ m, (spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n) :=
          Set.iUnion_unpair (fun n m ↦ spanningSets (μ.restrict (μ.sigmaFiniteSetGE ν n)) m
            ∩ μ.sigmaFiniteSetGE ν n)
    _ = ⋃ n, μ.sigmaFiniteSetGE ν n := by
        refine Set.iUnion_congr (fun n ↦ ?_)
        rw [← Set.iUnion_inter, iUnion_spanningSets, Set.univ_inter]
    _ = μ.sigmaFiniteSetWRT' ν := rfl

lemma measure_sigmaFiniteSetWRT' (μ ν : Measure α) [IsFiniteMeasure ν] :
    ν (μ.sigmaFiniteSetWRT' ν)
      = ⨆ (s) (_ : MeasurableSet s) (_ : SigmaFinite (μ.restrict s)), ν s := by
  apply le_antisymm
  · refine (le_iSup (f := fun _ ↦ _)
      (sigmaFinite_restrict_sigmaFiniteSetWRT' μ ν)).trans ?_
    exact le_iSup₂ (f := fun s _ ↦ ⨆ (_ : SigmaFinite (μ.restrict s)), ν s) (μ.sigmaFiniteSetWRT' ν)
      measurableSet_sigmaFiniteSetWRT'
  · exact le_of_tendsto' (tendsto_measure_sigmaFiniteSetGE μ ν)
      (fun _ ↦ measure_mono (Set.subset_iUnion _ _))

-- DISSOLVED: measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'_of_measurableSet

-- DISSOLVED: measure_eq_top_of_subset_compl_sigmaFiniteSetWRT'

end IsFiniteMeasure

section SFinite

-- DISSOLVED: measure_eq_top_of_subset_compl_sigmaFiniteSetWRT

lemma restrict_compl_sigmaFiniteSetWRT [SFinite ν] (hμν : μ ≪ ν) :
    μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ := by
  ext s
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' measurableSet_sigmaFiniteSetWRT.compl]
  by_cases hνs : ν (s ∩ (μ.sigmaFiniteSetWRT ν)ᶜ) = 0
  · rw [hνs, mul_zero]
    exact hμν hνs
  · rw [ENNReal.top_mul hνs, measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
      Set.inter_subset_right hνs]

end SFinite

@[simp]
lemma measure_compl_sigmaFiniteSetWRT (hμν : μ ≪ ν) [SigmaFinite μ] [SFinite ν] :
    ν (μ.sigmaFiniteSetWRT ν)ᶜ = 0 := by
  have h : ν (μ.sigmaFiniteSetWRT ν)ᶜ ≠ 0 → μ (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ :=
    measure_eq_top_of_subset_compl_sigmaFiniteSetWRT subset_rfl
  by_contra h0
  refine ENNReal.top_ne_zero ?_
  rw [← h h0, ← Measure.iSup_restrict_spanningSets]
  simp_rw [Measure.restrict_apply' (measurableSet_spanningSets μ _), ENNReal.iSup_eq_zero]
  intro i
  by_contra h_ne_zero
  have h_zero_top := measure_eq_top_of_subset_compl_sigmaFiniteSetWRT
    (Set.inter_subset_left : (μ.sigmaFiniteSetWRT ν)ᶜ ∩ spanningSets μ i ⊆ _) ?_
  swap; · exact fun h ↦ h_ne_zero (hμν h)
  refine absurd h_zero_top (ne_of_lt ?_)
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ i)

section SigmaFiniteSet

def Measure.sigmaFiniteSet (μ : Measure α) : Set α := μ.sigmaFiniteSetWRT μ

@[measurability]
lemma measurableSet_sigmaFiniteSet : MeasurableSet μ.sigmaFiniteSet :=
  measurableSet_sigmaFiniteSetWRT

lemma measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet [SFinite μ]
    (ht_subset : t ⊆ μ.sigmaFiniteSetᶜ) :
    μ t = 0 ∨ μ t = ∞ := by
  rw [or_iff_not_imp_left]
  exact measure_eq_top_of_subset_compl_sigmaFiniteSetWRT ht_subset

lemma restrict_compl_sigmaFiniteSet_eq_zero_or_top (μ : Measure α) [SFinite μ] (s : Set α) :
    μ.restrict μ.sigmaFiniteSetᶜ s = 0 ∨ μ.restrict μ.sigmaFiniteSetᶜ s = ∞ := by
  rw [Measure.restrict_apply' measurableSet_sigmaFiniteSet.compl]
  exact measure_eq_zero_or_top_of_subset_compl_sigmaFiniteSet Set.inter_subset_right

instance : SigmaFinite (μ.restrict μ.sigmaFiniteSet) := by
  rw [Measure.sigmaFiniteSet]
  infer_instance

lemma sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero (h : μ μ.sigmaFiniteSetᶜ = 0) :
    SigmaFinite μ := by
  rw [← Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_sigmaFiniteSet (μ := μ)),
    Measure.restrict_eq_zero.mpr h, add_zero]
  infer_instance

@[simp]
lemma measure_compl_sigmaFiniteSet (μ : Measure α) [SigmaFinite μ] : μ μ.sigmaFiniteSetᶜ = 0 :=
  measure_compl_sigmaFiniteSetWRT Measure.AbsolutelyContinuous.rfl

lemma measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite (μ : Measure α) :
    μ μ.sigmaFiniteSetᶜ = 0 ↔ SigmaFinite μ :=
  ⟨sigmaFinite_of_measure_compl_sigmaFiniteSet_eq_zero, fun _ ↦ measure_compl_sigmaFiniteSet μ⟩

end SigmaFiniteSet

end MeasureTheory
