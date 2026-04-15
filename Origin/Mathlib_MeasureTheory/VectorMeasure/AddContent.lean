/-
Extracted from MeasureTheory/VectorMeasure/AddContent.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Constructing a vector measure from an additive content

Consider a content defined on a semiring of sets. We investigate in this file
whether it is possible to extend it to a (countably additive) vector measure on the whole
sigma-algebra. We show that this is possible when the content is dominated by a finite
measure, see `exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom`.
-/

open MeasurableSpace

open scoped symmDiff

namespace MeasureTheory.VectorMeasure

variable {α : Type*} {hα : MeasurableSpace α} {E : Type*} [NormedAddCommGroup E]

[CompleteSpace E] {μ : Measure α}

def of_additive_of_le_measure
    (m : Set α → E) (hm : ∀ s, ‖m s‖ₑ ≤ μ s) [IsFiniteMeasure μ]
    (h'm : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → m (s ∪ t) = m s + m t)
    (h''m : ∀ s, ¬ MeasurableSet s → m s = 0) : VectorMeasure α E where
  measureOf' := m
  empty' := by simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
  not_measurable' := h''m
  m_iUnion' f f_meas f_disj := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]; swap
    · simp only [← toReal_enorm]
      apply ENNReal.summable_toReal
      apply ne_of_lt
      calc ∑' i, ‖m (f i)‖ₑ
      _ ≤ ∑' i, μ (f i) := by gcongr; apply hm
      _ = μ (⋃ i, f i) := (measure_iUnion f_disj f_meas).symm
      _ < ⊤ := measure_lt_top μ (⋃ i, f i)
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp_rw [norm_sub_rev, ← toReal_enorm, ← ENNReal.toReal_zero]
    apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    have A n : m (⋃ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range n, m (f i) := by
      induction n with
      | zero => simpa using h'm ∅ ∅ MeasurableSet.empty MeasurableSet.empty (by simp)
      | succ n ih =>
        simp only [Finset.range_add_one]
        rw [Finset.sum_insert (by simp)]
        simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
        rw [h'm _ _ (f_meas n), ih]
        · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
        · simp only [Finset.mem_range, Set.disjoint_iUnion_right]
          intro i hi
          exact f_disj hi.ne'
    have B n : m (⋃ i, f i) = m (⋃ i ∈ Finset.range n, f i) + m (⋃ i ∈ Set.Ici n, f i) := by
      have : ⋃ i, f i = (⋃ i ∈ Finset.range n, f i) ∪ (⋃ i ∈ Set.Ici n, f i) := by
        ext; simp; grind
      rw [this]
      apply h'm
      · exact Finset.measurableSet_biUnion _ (fun i hi ↦ f_meas i)
      · exact MeasurableSet.biUnion (Set.to_countable _) (fun i hi ↦ f_meas i)
      · simp only [Finset.mem_range, Set.mem_Ici, Set.disjoint_iUnion_right,
          Set.disjoint_iUnion_left]
        intro i hi j hj
        exact f_disj (hj.trans_le hi).ne
    have C n : m (⋃ i, f i) - ∑ i ∈ Finset.range n, m (f i) = m (⋃ i ∈ Set.Ici n, f i) := by
      rw [B n, A]; simp
    simp only [C]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h := fun n ↦ μ (⋃ i ∈ Set.Ici n, f i)) ?_ (fun i ↦ bot_le) (fun i ↦ hm _)
    exact tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
      (fun i ↦ (f_meas i).nullMeasurableSet) f_disj

open scoped ENNReal

set_option backward.isDefEq.respectTransparency false in

lemma exists_extension_of_isSetSemiring_of_le_measure_of_dense [IsFiniteMeasure μ]
    {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hCmeas : ∀ s ∈ C, MeasurableSet s) (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : ∀ t ε, MeasurableSet t → 0 < ε → ∃ s ∈ supClosure C, μ (s ∆ t) < ε) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  set m₀ : AddContent E (supClosure C) := m.supClosure hC with hm₀
  have A (s) (hs : s ∈ supClosure C) : ‖m₀ s‖ₑ ≤ μ s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    nth_rewrite 2 [← P.sup_parts]
    rw [hm₀, AddContent.supClosure_apply_finpartition hC _ PC, Finset.sup_set_eq_biUnion,
      measure_biUnion_finset P.disjoint (fun b hb ↦ hCmeas _ (PC hb))]
    apply (enorm_sum_le _ _).trans
    gcongr with t ht
    exact hm _ (PC ht)
  have B (s) (hs : s ∈ supClosure C) : MeasurableSet s := by
    rw [hC.mem_supClosure_iff] at hs
    rcases hs with ⟨P, PC⟩
    rw [← P.sup_parts, Finset.sup_set_eq_biUnion]
    exact Finset.measurableSet_biUnion _ (fun b hb ↦ hCmeas _ (PC hb))
  rcases VectorMeasure.exists_extension_of_isSetRing_of_le_measure_of_dense
    hC.isSetRing_supClosure B A h'C with ⟨m', hm', m'bound⟩
  refine ⟨m', fun s hs ↦ ?_, m'bound⟩
  rw [hm' _ (subset_supClosure hs)]
  exact AddContent.supClosure_apply_of_mem _ _ hs

private lemma exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s)
    (h'C : hα = generateFrom C) (h''C : ∃ D : Set (Set α), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  apply VectorMeasure.exists_extension_of_isSetSemiring_of_le_measure_of_dense hC ?_ hm ?_
  · intro s hs
    rw [h'C]
    exact measurableSet_generateFrom hs
  · intro t ε ht εpos
    exact exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring hC h''C h'C ht εpos

theorem exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom
    [IsFiniteMeasure μ] {C : Set (Set α)} {m : AddContent E C} (hC : IsSetSemiring C)
    (hm : ∀ s ∈ C, ‖m s‖ₑ ≤ μ s) (h'C : hα = generateFrom C) :
    ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ s := by
  have M (s) (hs : s ∈ C) : MeasurableSet s := by
    rw [h'C]; exact measurableSet_generateFrom hs
  rcases Measure.exists_ae_subset_biUnion_countable μ M with ⟨D, DC, D_count, hD⟩
  have MD : MeasurableSet (⋃₀ D) := MeasurableSet.sUnion D_count (fun t ht ↦ M _ (DC ht))
  let μ' := μ.restrict (⋃₀ D)
  obtain ⟨m', h, h'⟩ : ∃ m' : VectorMeasure α E, (∀ s ∈ C, m' s = m s) ∧ ∀ s, ‖m' s‖ₑ ≤ μ' s := by
    apply exists_extension_of_isSetSemiring_of_le_measure_of_generateFrom_of_cover hC
      (fun s hs ↦ ?_) h'C ?_
    · exact ⟨D, D_count, DC, by simp [μ', Measure.restrict_apply' MD]⟩
    · apply (hm s hs).trans
      simp only [Measure.restrict_apply' MD, μ']
      apply measure_mono_ae
      nth_rewrite 1 [← Set.inter_self s]
      exact ae_le_set_inter Filter.EventuallyLE.rfl (hD s hs)
  exact ⟨m', h, fun s ↦ (h' s).trans (Measure.restrict_apply_le (⋃₀ D) s)⟩

end MeasureTheory.VectorMeasure
