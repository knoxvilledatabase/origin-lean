/-
Extracted from MeasureTheory/Measure/Hausdorff.lean
Genuine: 16 of 17 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (ediam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, ediam (t n) ≤ r), ∑' n, ediam (t n) ^ d
```

For every set `s` and any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`MeasureTheory.Measure.hausdorffMeasure_zero_or_top`. In
`Mathlib/Topology/MetricSpace/HausdorffDimension.lean` we use this fact to define the Hausdorff
dimension `dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`MeasureTheory.Measure.mkMetric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `MeasureTheory.Measure.mkMetric'`) we use any function
of `m : Set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : Set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `MeasureTheory.extend m`.

We also define a predicate `MeasureTheory.OuterMeasure.IsMetric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mkMetric'` are metric outer
measures.

## Main definitions

* `MeasureTheory.OuterMeasure.IsMetric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Carathéodory condition, see
  `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`.
* `MeasureTheory.OuterMeasure.mkMetric'` and its particular case
  `MeasureTheory.OuterMeasure.mkMetric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `MeasureTheory.Measure.mkMetric'` and
  `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬Set.Subsingleton (t n)), (ediam (t n)) ^ d`,
  see `MeasureTheory.Measure.hausdorffMeasure_apply`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬Set.Subsingleton (t n))` part.

## Main statements

### Basic properties

* `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Carathéodory measurable (hence, `μ` defines an actual
  `MeasureTheory.Measure`). See also `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `MeasureTheory.Measure.noAtoms_hausdorff`: Hausdorff measure has no atoms.

### Hausdorff measure in `ℝⁿ`

* `MeasureTheory.hausdorffMeasure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notation

We use the following notation localized in `MeasureTheory`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/

open scoped NNReal ENNReal Topology

open Metric EMetric Set Function Filter Encodable Module TopologicalSpace

noncomputable section

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

namespace MeasureTheory

namespace OuterMeasure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Carathéodory's theorem: a metric outer
measure has the Carathéodory property.
-/

def IsMetric (μ : OuterMeasure X) : Prop :=
  ∀ s t : Set X, Metric.AreSeparated s t → μ (s ∪ t) = μ s + μ t

namespace IsMetric

variable {μ : OuterMeasure X}

theorem finset_iUnion_of_pairwise_separated (hm : IsMetric μ) {I : Finset ι} {s : ι → Set X}
    (hI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Metric.AreSeparated (s i) (s j)) :
    μ (⋃ i ∈ I, s i) = ∑ i ∈ I, μ (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ihI =>
    simp only [Finset.mem_insert] at hI
    rw [Finset.set_biUnion_insert, hm, ihI, Finset.sum_insert hiI]
    exacts [fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      Metric.AreSeparated.finset_iUnion_right fun j hj =>
        hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

theorem borel_le_caratheodory (hm : IsMetric μ) : borel X ≤ μ.caratheodory := by
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun t ht => μ.isCaratheodory_iff_le.2 fun s => ?_
  set S : ℕ → Set X := fun n => {x ∈ s | (↑n)⁻¹ ≤ infEDist x t}
  have Ssep (n) : Metric.AreSeparated (S n) t :=
    ⟨n⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _),
      fun x hx y hy ↦ hx.2.trans <| infEDist_le_edist_of_mem hy⟩
  have Ssep' : ∀ n, Metric.AreSeparated (S n) (s ∩ t) := fun n =>
    (Ssep n).mono Subset.rfl inter_subset_right
  have S_sub : ∀ n, S n ⊆ s \ t := fun n =>
    subset_inter inter_subset_left (Ssep n).subset_compl_right
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s := fun n =>
    calc
      μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) := Eq.symm <| hm _ _ <| (Ssep' n).symm
      _ ≤ μ (s ∩ t ∪ s \ t) := μ.mono <| union_subset_union_right _ <| S_sub n
      _ = μ s := by rw [inter_union_diff]
  have iUnion_S : ⋃ n, S n = s \ t := by
    refine Subset.antisymm (iUnion_subset S_sub) ?_
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_infEDist_zero_of_closed ht] at hxt
    rcases ENNReal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞
  · rw [htop, add_top, ← htop]
    exact μ.mono diff_subset
  suffices μ (⋃ n, S n) ≤ ⨆ n, μ (S n) by calc
    μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) := by rw [iUnion_S]
    _ ≤ μ (s ∩ t) + ⨆ n, μ (S n) := by gcongr
    _ = ⨆ n, μ (s ∩ t) + μ (S n) := ENNReal.add_iSup ..
    _ ≤ μ s := iSup_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : ∀ n, S n ⊆ S (n + 1) := fun n x hx =>
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 n.le_succ) hx.2⟩
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top this ?_).le; clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable, ENNReal.add_ne_top]
  suffices ∀ a, (∑' k : ℕ, μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  refine fun r => ne_top_of_le_ne_top htop ?_
  rw [← iUnion_S, ENNReal.tsum_eq_iSup_nat, iSup_le_iff]
  intro n
  rw [← hm.finset_iUnion_of_pairwise_separated]
  · exact μ.mono (iUnion_subset fun i => iUnion_subset fun _ x hx => mem_iUnion.2 ⟨_, hx.1⟩)
  suffices ∀ i j, i < j → Metric.AreSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r)) from
    fun i _ j _ hij => hij.lt_or_gt.elim
      (fun h => (this i j h).mono inter_subset_left fun x hx => by exact ⟨hx.1.1, hx.2⟩)
      fun h => (this j i h).symm.mono (fun x hx => by exact ⟨hx.1.1, hx.2⟩) inter_subset_left
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [ENNReal.inv_lt_inv, Nat.cast_lt]; lia
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa [tsub_eq_zero_iff_le] using A,
    fun x hx y hy => ?_⟩
  have : infEDist y t < (↑(2 * j + r))⁻¹ := not_le.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases infEDist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z := le_infEDist.1 hx.2 _ hzt
  apply ENNReal.le_of_add_le_add_right hyz.ne_top
  refine le_trans ?_ (edist_triangle _ _ _)
  refine (add_le_add le_rfl hyz.le).trans (Eq.trans_le ?_ hxz)
  rw [tsub_add_cancel_of_le A.le]

theorem le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ) :
    ‹MeasurableSpace X› ≤ μ.caratheodory := by
  rw [BorelSpace.measurable_eq (α := X)]
  exact hm.borel_le_caratheodory

end IsMetric

/-!
### Constructors of metric outer measures

In this section we provide constructors `MeasureTheory.OuterMeasure.mkMetric'` and
`MeasureTheory.OuterMeasure.mkMetric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/

def mkMetric'.pre (m : Set X → ℝ≥0∞) (r : ℝ≥0∞) : OuterMeasure X :=
  boundedBy <| extend fun s (_ : ediam s ≤ r) => m s

def mkMetric' (m : Set X → ℝ≥0∞) : OuterMeasure X :=
  ⨆ r > 0, mkMetric'.pre m r

def mkMetric (m : ℝ≥0∞ → ℝ≥0∞) : OuterMeasure X :=
  mkMetric' fun s => m (ediam s)

namespace mkMetric'

variable {m : Set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : OuterMeasure X} {s : Set X}

theorem le_pre : μ ≤ pre m r ↔ ∀ s : Set X, ediam s ≤ r → μ s ≤ m s := by
  simp only [pre, le_boundedBy, extend, le_iInf_iff]

theorem pre_le (hs : ediam s ≤ r) : pre m r s ≤ m s :=
  (boundedBy_le _).trans <| iInf_le _ hs

theorem mono_pre (m : Set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') : pre m r' ≤ pre m r :=
  le_pre.2 fun _ hs => pre_le (hs.trans h)

theorem mono_pre_nat (m : Set X → ℝ≥0∞) : Monotone fun k : ℕ => pre m k⁻¹ :=
  fun k l h => le_pre.2 fun _ hs => pre_le (hs.trans <| by simpa)

theorem tendsto_pre (m : Set X → ℝ≥0∞) (s : Set X) :
    Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric' m s) := by
  rw [← tendsto_comp_coe_Ioi_atBot]
  simp only [mkMetric', OuterMeasure.iSup_apply, iSup_subtype']
  exact tendsto_atBot_iSup fun r r' hr => mono_pre _ hr _

theorem tendsto_pre_nat (m : Set X → ℝ≥0∞) (s : Set X) :
    Tendsto (fun n : ℕ => pre m n⁻¹ s) atTop (𝓝 <| mkMetric' m s) := by
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ENNReal.tendsto_inv_nat_nhds_zero, ?_⟩)
  refine tendsto_principal.2 (Eventually.of_forall fun n => ?_)
  simp

theorem eq_iSup_nat (m : Set X → ℝ≥0∞) : mkMetric' m = ⨆ n : ℕ, mkMetric'.pre m n⁻¹ := by
  ext1 s
  rw [iSup_apply]
  refine tendsto_nhds_unique (mkMetric'.tendsto_pre_nat m s)
    (tendsto_atTop_iSup fun k l hkl => mkMetric'.mono_pre_nat m hkl s)

theorem trim_pre [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X → ℝ≥0∞)
    (hcl : ∀ s, m (closure s) = m s) (r : ℝ≥0∞) : (pre m r).trim = pre m r := by
  refine le_antisymm (le_pre.2 fun s hs => ?_) (le_trim _)
  rw [trim_eq_iInf]
  refine iInf_le_of_le (closure s) <| iInf_le_of_le subset_closure <|
    iInf_le_of_le measurableSet_closure ((pre_le ?_).trans_eq (hcl _))
  rwa [ediam_closure]

end mkMetric'

theorem mkMetric'_isMetric (m : Set X → ℝ≥0∞) : (mkMetric' m).IsMetric := by
  rintro s t ⟨r, r0, hr⟩
  refine tendsto_nhds_unique_of_eventuallyEq
    (mkMetric'.tendsto_pre _ _) ((mkMetric'.tendsto_pre _ _).add (mkMetric'.tendsto_pre _ _)) ?_
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhdsGT r0]
  rintro ε ⟨_, εr⟩
  refine boundedBy_union_of_top_of_nonempty_inter ?_
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < ediam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_ediam_of_mem hxu hyu)
  exact iInf_eq_top.2 fun h => (this.not_ge h).elim

-- DISSOLVED: mkMetric_mono_smul
