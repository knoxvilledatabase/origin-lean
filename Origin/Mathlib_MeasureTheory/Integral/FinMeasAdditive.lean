/-
Extracted from MeasureTheory/Integral/FinMeasAdditive.lean
Genuine: 20 of 22 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additivity on measurable sets with finite measure

Let `T : Set α → E →L[ℝ] F` be additive for measurable sets with finite measure, in the sense that
for `s, t` two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`. `T` is akin to a bilinear map on
`Set α × E`, or a linear map on indicator functions.

This property is named `FinMeasAdditive` in this file. We also define `DominatedFinMeasAdditive`,
which requires in addition that the norm on every set is less than the measure of the set
(up to a multiplicative constant); in `Mathlib/MeasureTheory/Integral/SetToL1.lean` we extend
set functions with this stronger property to integrable (L1) functions.

## Main definitions

- `FinMeasAdditive μ T`: the property that `T` is additive on measurable sets with finite measure.
  For two such sets, `Disjoint s t → T (s ∪ t) = T s + T t`.
- `DominatedFinMeasAdditive μ T C`: `FinMeasAdditive μ T ∧ ∀ s, ‖T s‖ ≤ C * μ.real s`.
  This is the property needed to perform the extension from indicators to L1.

## Implementation notes

The starting object `T : Set α → E →L[ℝ] F` matters only through its restriction on measurable sets
with finite measure. Its value on other sets is ignored.
-/

noncomputable section

open Set Filter ENNReal Finset

namespace MeasureTheory

variable {α E F F' G 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup G] {m : MeasurableSpace α} {μ : Measure α}

local infixr:25 " →ₛ " => SimpleFunc

section FinMeasAdditive

def FinMeasAdditive {β} [AddMonoid β] {_ : MeasurableSpace α} (μ : Measure α) (T : Set α → β) :
    Prop :=
  ∀ s t, MeasurableSet s → MeasurableSet t → μ s ≠ ∞ → μ t ≠ ∞ → Disjoint s t →
    T (s ∪ t) = T s + T t

namespace FinMeasAdditive

variable {β : Type*} [AddCommMonoid β] {T T' : Set α → β}

theorem zero : FinMeasAdditive μ (0 : Set α → β) := fun _ _ _ _ _ _ _ => by simp

theorem add (hT : FinMeasAdditive μ T) (hT' : FinMeasAdditive μ T') :
    FinMeasAdditive μ (T + T') := by
  intro s t hs ht hμs hμt hst
  simp only [hT s t hs ht hμs hμt hst, hT' s t hs ht hμs hμt hst, Pi.add_apply]
  abel

theorem smul [DistribSMul 𝕜 β] (hT : FinMeasAdditive μ T) (c : 𝕜) :
    FinMeasAdditive μ fun s => c • T s := fun s t hs ht hμs hμt hst => by
  simp [hT s t hs ht hμs hμt hst]

theorem of_eq_top_imp_eq_top {μ' : Measure α} (h : ∀ s, MeasurableSet s → μ s = ∞ → μ' s = ∞)
    (hT : FinMeasAdditive μ T) : FinMeasAdditive μ' T := fun s t hs ht hμ's hμ't hst =>
  hT s t hs ht (mt (h s hs) hμ's) (mt (h t ht) hμ't) hst

theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : FinMeasAdditive (c • μ) T) :
    FinMeasAdditive μ T := by
  refine of_eq_top_imp_eq_top (fun s _ hμs => ?_) hT
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_eq_top] at hμs
  simp only [hc_ne_top, or_false, Ne, false_and] at hμs
  exact hμs.2

-- DISSOLVED: smul_measure

-- DISSOLVED: smul_measure_iff

theorem map_empty_eq_zero {β} [AddCancelMonoid β] {T : Set α → β} (hT : FinMeasAdditive μ T) :
    T ∅ = 0 := by
  have h_empty : μ ∅ ≠ ∞ := (measure_empty.le.trans_lt ENNReal.coe_lt_top).ne
  specialize hT ∅ ∅ MeasurableSet.empty MeasurableSet.empty h_empty h_empty (disjoint_empty _)
  rw [Set.union_empty] at hT
  nth_rw 1 [← add_zero (T ∅)] at hT
  exact (add_left_cancel hT).symm

theorem map_iUnion_fin_meas_set_eq_sum (T : Set α → β) (T_empty : T ∅ = 0)
    (h_add : FinMeasAdditive μ T) {ι} (S : ι → Set α) (sι : Finset ι)
    (hS_meas : ∀ i, MeasurableSet (S i)) (hSp : ∀ i ∈ sι, μ (S i) ≠ ∞)
    (h_disj : ∀ᵉ (i ∈ sι) (j ∈ sι), i ≠ j → Disjoint (S i) (S j)) :
    T (⋃ i ∈ sι, S i) = ∑ i ∈ sι, T (S i) := by
  classical
  revert hSp h_disj
  refine Finset.induction_on sι ?_ ?_
  · simp only [Finset.notMem_empty, IsEmpty.forall_iff, iUnion_false, iUnion_empty, sum_empty,
      imp_true_iff, T_empty]
  intro a s has h hps h_disj
  rw [Finset.sum_insert has, ← h]
  swap; · exact fun i hi => hps i (Finset.mem_insert_of_mem hi)
  swap
  · exact fun i hi j hj hij =>
      h_disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
  rw [←
    h_add (S a) (⋃ i ∈ s, S i) (hS_meas a) (measurableSet_biUnion _ fun i _ => hS_meas i)
      (hps a (Finset.mem_insert_self a s))]
  · congr; convert Finset.iSup_insert a s S
  · exact (measure_biUnion_lt_top s.finite_toSet fun i hi ↦
      (hps i <| Finset.mem_insert_of_mem hi).lt_top).ne
  · simp_rw [Set.disjoint_iUnion_right]
    intro i hi
    refine h_disj a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) fun hai ↦ ?_
    rw [← hai] at hi
    exact has hi

end FinMeasAdditive

def DominatedFinMeasAdditive {β} [SeminormedAddCommGroup β] {_ : MeasurableSpace α} (μ : Measure α)
    (T : Set α → β) (C : ℝ) : Prop :=
  FinMeasAdditive μ T ∧ ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s

namespace DominatedFinMeasAdditive

variable {β : Type*} [SeminormedAddCommGroup β] {T T' : Set α → β} {C C' : ℝ}

theorem zero {m : MeasurableSpace α} (μ : Measure α) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ (0 : Set α → β) C := by
  refine ⟨FinMeasAdditive.zero, fun s _ _ => ?_⟩
  rw [Pi.zero_apply, norm_zero]
  exact mul_nonneg hC toReal_nonneg

theorem eq_zero_of_measure_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ}
    (hT : DominatedFinMeasAdditive μ T C) {s : Set α} (hs : MeasurableSet s) (hs_zero : μ s = 0) :
    T s = 0 := by
  refine norm_eq_zero.mp ?_
  refine ((hT.2 s hs (by simp [hs_zero])).trans (le_of_eq ?_)).antisymm (norm_nonneg _)
  rw [measureReal_def, hs_zero, ENNReal.toReal_zero, mul_zero]

theorem eq_zero {β : Type*} [NormedAddCommGroup β] {T : Set α → β} {C : ℝ} {_ : MeasurableSpace α}
    (hT : DominatedFinMeasAdditive (0 : Measure α) T C) {s : Set α} (hs : MeasurableSet s) :
    T s = 0 :=
  eq_zero_of_measure_zero hT hs (by simp only [Measure.coe_zero, Pi.zero_apply])

theorem add (hT : DominatedFinMeasAdditive μ T C) (hT' : DominatedFinMeasAdditive μ T' C') :
    DominatedFinMeasAdditive μ (T + T') (C + C') := by
  refine ⟨hT.1.add hT'.1, fun s hs hμs => ?_⟩
  rw [Pi.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hT.2 s hs hμs) (hT'.2 s hs hμs))

theorem smul [SeminormedAddGroup 𝕜] [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β]
    (hT : DominatedFinMeasAdditive μ T C) (c : 𝕜) :
    DominatedFinMeasAdditive μ (fun s => c • T s) (‖c‖ * C) := by
  refine ⟨hT.1.smul c, fun s hs hμs => (norm_smul_le _ _).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul le_rfl (hT.2 s hs hμs) (norm_nonneg _) (norm_nonneg _)

theorem of_measure_le {μ' : Measure α} (h : μ ≤ μ') (hT : DominatedFinMeasAdditive μ T C)
    (hC : 0 ≤ C) : DominatedFinMeasAdditive μ' T C := by
  have h' : ∀ s, μ s = ∞ → μ' s = ∞ := fun s hs ↦ top_unique <| hs.symm.trans_le (h _)
  refine ⟨hT.1.of_eq_top_imp_eq_top fun s _ ↦ h' s, fun s hs hμ's ↦ ?_⟩
  have hμs : μ s < ∞ := (h s).trans_lt hμ's
  calc
    ‖T s‖ ≤ C * μ.real s := hT.2 s hs hμs
    _ ≤ C * μ'.real s := by
      simp only [measureReal_def]
      gcongr
      exact hμ's.ne

theorem add_measure_right {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_right le_rfl) hT hC

theorem add_measure_left {_ : MeasurableSpace α} (μ ν : Measure α)
    (hT : DominatedFinMeasAdditive ν T C) (hC : 0 ≤ C) : DominatedFinMeasAdditive (μ + ν) T C :=
  of_measure_le (Measure.le_add_left le_rfl) hT hC

theorem of_smul_measure {c : ℝ≥0∞} (hc_ne_top : c ≠ ∞) (hT : DominatedFinMeasAdditive (c • μ) T C) :
    DominatedFinMeasAdditive μ T (c.toReal * C) := by
  have h : ∀ s, MeasurableSet s → c • μ s = ∞ → μ s = ∞ := by
    intro s _ hcμs
    simp only [hc_ne_top, smul_eq_mul, ENNReal.mul_eq_top, or_false, Ne,
      false_and] at hcμs
    exact hcμs.2
  refine ⟨hT.1.of_eq_top_imp_eq_top (μ := c • μ) h, fun s hs hμs => ?_⟩
  have hcμs : c • μ s ≠ ∞ := mt (h s hs) hμs.ne
  rw [smul_eq_mul] at hcμs
  refine (hT.2 s hs hcμs.lt_top).trans (le_of_eq ?_)
  simp only [measureReal_ennreal_smul_apply]
  ring

theorem of_measure_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞) (h : μ ≤ c • μ')
    (hT : DominatedFinMeasAdditive μ T C) (hC : 0 ≤ C) :
    DominatedFinMeasAdditive μ' T (c.toReal * C) :=
  (hT.of_measure_le h hC).of_smul_measure hc

end DominatedFinMeasAdditive

end FinMeasAdditive

namespace SimpleFunc

def setToSimpleFunc {_ : MeasurableSpace α} (T : Set α → F →L[ℝ] F') (f : α →ₛ F) : F' :=
  ∑ x ∈ f.range, T (f ⁻¹' {x}) x
