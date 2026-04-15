/-
Extracted from MeasureTheory/Function/AbsolutelyContinuous.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `uIcc a b` and proves some
basic properties about absolutely continuous functions.

A function `f` is *absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such
that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`,
`b i` are all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`.

We give a filter version of the definition of absolutely continuous functions in
`AbsolutelyContinuousOnInterval` based on `AbsolutelyContinuousOnInterval.totalLengthFilter`
and `AbsolutelyContinuousOnInterval.disjWithin` and prove its equivalence with the `ε`-`δ`
definition in `absolutelyContinuousOnInterval_iff`.

We use the filter version to prove that absolutely continuous functions are closed under
* addition - `AbsolutelyContinuousOnInterval.add`;
* negation - `AbsolutelyContinuousOnInterval.neg`;
* subtraction - `AbsolutelyContinuousOnInterval.sub`;
* scalar multiplication - `AbsolutelyContinuousOnInterval.const_smul`,
  `AbsolutelyContinuousOnInterval.const_mul`;
* multiplication - `AbsolutelyContinuousOnInterval.smul`,
  `AbsolutelyContinuousOnInterval.mul`;

and that absolutely continuous implies uniformly continuous in
`AbsolutelyContinuousOnInterval.uniformContinuousOn`.

We use the `ε`-`δ` definition to prove that
* Lipschitz continuous functions are absolutely continuous -
  `LipschitzOnWith.absolutelyContinuousOnInterval`;
* absolutely continuous functions have bounded variation -
  `AbsolutelyContinuousOnInterval.boundedVariationOn`.

We conclude that
* absolutely continuous functions are a.e. differentiable -
  `AbsolutelyContinuousOnInterval.ae_differentiableAt`;
* if `f` is integrable on `uIcc a b`, then for any `c` in `uIcc a b`, `fun x ↦ ∫ v in c..x, f v`
  is absolutely continuous on `uIcc a b` -
  `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.

## Tags
absolutely continuous
-/

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

open Set Filter Function MeasureTheory

open scoped Topology NNReal

namespace AbsolutelyContinuousOnInterval

def totalLengthFilter : Filter (ℕ × (ℕ → X × X)) := Filter.comap
  (fun E ↦ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)

lemma hasBasis_totalLengthFilter : totalLengthFilter.HasBasis (fun (ε : ℝ) => 0 < ε)
    (fun (ε : ℝ) =>
      {E : ℕ × (ℕ → X × X) | ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < ε}) := by
  convert Filter.HasBasis.comap (α := ℝ) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_setOf_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 ≤ ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

def disjWithin (a b : ℝ) := {E : ℕ × (ℕ → ℝ × ℝ) |
  (∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (E.2 i).1 (E.2 i).2)}

lemma disjWithin_comm (a b : ℝ) : disjWithin a b = disjWithin b a := by
  rw [disjWithin, disjWithin, uIcc_comm]

lemma disjWithin_mono {a b c d : ℝ} (habcd : uIcc c d ⊆ uIcc a b) :
    disjWithin c d ⊆ disjWithin a b := by
  grind [disjWithin]

lemma uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) {i : ℕ} (hi : i < n) : uIoc (I i).1 (I i).2 ⊆ uIoc a b := by
  simp only [disjWithin, Finset.mem_range, mem_setOf_eq, uIcc, mem_Icc] at hnI
  grind

lemma biUnion_uIoc_subset_of_mem_disjWithin {a b : ℝ} {n : ℕ} {I : ℕ → ℝ × ℝ}
    (hnI : (n, I) ∈ disjWithin a b) :
    (⋃ i ∈ Finset.range n, uIoc (I i).1 (I i).2) ⊆ uIoc a b := by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi ↦ uIoc_subset_of_mem_disjWithin hnI hi

lemma tendsto_volume_totalLengthFilter_nhds_zero :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
    totalLengthFilter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E ↦ ENNReal.ofReal (∑ i ∈ Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_finset_le]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ dist_nonneg)]
    apply Eq.le
    apply Finset.sum_congr rfl
    simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']

lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : ℝ) :
    Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume.restrict (uIoc a b)
        (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ volume (⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finset.mem_range]
    apply Measure.restrict_le_self

def _root_.AbsolutelyContinuousOnInterval (f : ℝ → X) (a b : ℝ) :=
  Tendsto (fun E ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

theorem _root_.absolutelyContinuousOnInterval_iff (f : ℝ → X) (a b : ℝ) :
    AbsolutelyContinuousOnInterval f a b ↔
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ E, E ∈ disjWithin a b →
    ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ →
    ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))]

variable {f g : ℝ → X} {a b c d : ℝ}

theorem symm (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]

theorem mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d ⊆ uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

variable {f g : ℝ → F}
