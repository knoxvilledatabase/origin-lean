/-
Extracted from MeasureTheory/Measure/MeasureSpace.lean
Genuine: 23 of 24 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Measure spaces

The definition of a measure and a measure space are in `MeasureTheory.MeasureSpaceDef`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `MeasureSpaceDef`, and to
be available in `MeasureSpace` (through `MeasurableSpace`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `Measure.ofMeasurable` and `OuterMeasure.toMeasure` are two important ways to define a measure.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `Measure.ofMeasurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `OuterMeasure.toMeasure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generateFrom_of_iUnion`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generateFrom_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generateFrom_of_iUnion` using
  `C ∪ {univ}`, but is easier to work with.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace Topology Filter ENNReal NNReal Interval MeasureTheory

open scoped symmDiff

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory

variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

-- INSTANCE (free from Core): ae_isMeasurablyGenerated

theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ ∀ᵐ x ∂μ, x ∈ Ioc b a → P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]

theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint

theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint

theorem measure_inter_add_diff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_diff₀ _ ht.nullMeasurableSet

theorem measure_diff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_diff s ht)

theorem measure_diff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
  contrapose! hs
  exact ((measure_mono (subset_diff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff (s ∪ t) ht, Set.union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff s ht]
  ac_rfl

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]

lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
  measure_mono_top subset_union_right (measure_diff_eq_top ht hs)

theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet

theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]

theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]

theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm

theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ ↦ Subset.rfl

theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))

theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]

theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]
