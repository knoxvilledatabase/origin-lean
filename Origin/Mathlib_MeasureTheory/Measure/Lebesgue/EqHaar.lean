/-
Extracted from MeasureTheory/Measure/Lebesgue/EqHaar.lean
Genuine: 12 of 14 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`MeasureTheory.addHaarMeasure_eq_volume` and `MeasureTheory.addHaarMeasure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite-dimensional real vector space:
* `map_linearMap_addHaar_eq_smul_addHaar`: a linear map rescales the Haar measure by the
  absolute value of its determinant.
* `addHaar_preimage_linearMap` : when `f` is a linear map with nonzero determinant, the measure
  of `f ⁻¹' s` is the measure of `s` multiplied by the absolute value of the inverse of the
  determinant of `f`.
* `addHaar_image_linearMap` : when `f` is a linear map, the measure of `f '' s` is the
  measure of `s` multiplied by the absolute value of the determinant of `f`.
* `addHaar_submodule` : a strict submodule has measure `0`.
* `addHaar_smul` : the measure of `r • s` is `|r| ^ dim * μ s`.
* `addHaar_ball`: the measure of `ball x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_closedBall`: the measure of `closedBall x r` is `r ^ dim * μ (ball 0 1)`.
* `addHaar_sphere`: spheres have zero measure.

This makes it possible to associate a Lebesgue measure to an `n`-alternating map in dimension `n`.
This measure is called `AlternatingMap.measure`. Its main property is
`ω.measure_parallelepiped v`, stating that the associated measure of the parallelepiped spanned
by vectors `v₁, ..., vₙ` is given by `|ω v|`.

We also show that a Lebesgue density point `x` of a set `s` (with respect to closed balls) has
density one for the rescaled copies `{x} + r • t` of a given set `t` with positive measure, in
`tendsto_addHaar_inter_smul_one_of_density_one`. In particular, `s` intersects `{x} + r • t` for
small `r`, see `eventually_nonempty_inter_smul_of_density_one`.

Statements on integrals of functions with respect to an additive Haar measure can be found in
`MeasureTheory.Measure.Haar.NormedSpace`.
-/

assert_not_exists MeasureTheory.integral

open TopologicalSpace Set Filter Metric Bornology

open scoped ENNReal Pointwise Topology NNReal

def TopologicalSpace.PositiveCompacts.Icc01 : PositiveCompacts ℝ where
  carrier := Icc 0 1
  isCompact' := isCompact_Icc
  interior_nonempty' := by simp_rw [interior_Icc, nonempty_Ioo, zero_lt_one]

universe u

def TopologicalSpace.PositiveCompacts.piIcc01 (ι : Type*) [Finite ι] :
    PositiveCompacts (ι → ℝ) where
  carrier := pi univ fun _ => Icc 0 1
  isCompact' := isCompact_univ_pi fun _ => isCompact_Icc
  interior_nonempty' := by
    simp only [interior_pi_set, Set.toFinite, interior_Icc, univ_pi_nonempty_iff, nonempty_Ioo,
      imp_true_iff, zero_lt_one]

namespace Module.Basis

theorem parallelepiped_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).parallelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι :=
  SetLike.coe_injective <| by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert parallelepiped_single (ι := ι) 1
    · exact zero_le_one

theorem parallelepiped_eq_map {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Basis ι ℝ E) :
    b.parallelepiped = (PositiveCompacts.piIcc01 ι).map b.equivFun.symm
      b.equivFunL.symm.continuous b.equivFunL.symm.isOpenMap := by
  classical
  rw [← Basis.parallelepiped_basisFun, ← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

open MeasureTheory MeasureTheory.Measure

theorem map_addHaar {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]
    (b : Basis ι ℝ E) (f : E ≃L[ℝ] F) :
    map f b.addHaar = (b.map f.toLinearEquiv).addHaar := by
  rw [eq_comm, Basis.addHaar_eq_iff, Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet, Basis.coe_parallelepiped, Basis.coe_map]
  erw [← image_parallelepiped, f.toEquiv.preimage_image, addHaar_self]

end Module.Basis

namespace MeasureTheory

open Measure TopologicalSpace.PositiveCompacts Module

/-!
### The Lebesgue measure is a Haar measure on `ℝ` and on `ℝ^ι`.
-/

theorem addHaarMeasure_eq_volume : addHaarMeasure Icc01 = volume := by
  convert (addHaarMeasure_unique volume Icc01).symm; simp [Icc01]

theorem addHaarMeasure_eq_volume_pi (ι : Type*) [Fintype ι] :
    addHaarMeasure (piIcc01 ι) = volume := by
  convert (addHaarMeasure_unique volume (piIcc01 ι)).symm
  simp only [piIcc01, volume_pi_pi fun _ => Icc (0 : ℝ) 1, PositiveCompacts.coe_mk,
    Compacts.coe_mk, Finset.prod_const_one, ENNReal.ofReal_one, Real.volume_Icc, one_smul, sub_zero]

theorem isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  inferInstance

namespace Measure

/-!
### Strict subspaces have zero measure
-/

open scoped Function -- required for scoped `on` notation

theorem addHaar_eq_zero_of_disjoint_translates_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (sb : IsBounded s) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  by_contra h
  apply lt_irrefl ∞
  calc
    ∞ = ∑' _ : ℕ, μ s := (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
    _ = ∑' n : ℕ, μ ({u n} + s) := by
      congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
    _ = μ (⋃ n, {u n} + s) := Eq.symm <| measure_iUnion hs fun n => by
      simpa only [image_add_left, singleton_add] using measurable_id.const_add _ h's
    _ = μ (range u + s) := by rw [← iUnion_add, iUnion_singleton_eq_range]
    _ < ∞ := (hu.add sb).measure_lt_top

theorem addHaar_eq_zero_of_disjoint_translates {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
    [IsAddHaarMeasure μ] {s : Set E} (u : ℕ → E) (hu : IsBounded (range u))
    (hs : Pairwise (Disjoint on fun n => {u n} + s)) (h's : MeasurableSet s) : μ s = 0 := by
  suffices H : ∀ R, μ (s ∩ closedBall 0 R) = 0 by
    apply le_antisymm _ (zero_le _)
    calc
      μ s ≤ ∑' n : ℕ, μ (s ∩ closedBall 0 n) := by
        conv_lhs => rw [← iUnion_inter_closedBall_nat s 0]
        exact measure_iUnion_le _
      _ = 0 := by simp only [H, tsum_zero]
  intro R
  apply addHaar_eq_zero_of_disjoint_translates_aux μ u
    (isBounded_closedBall.subset inter_subset_right) hu _ (h's.inter measurableSet_closedBall)
  refine pairwise_disjoint_mono hs fun n => ?_
  exact add_subset_add Subset.rfl inter_subset_left

theorem addHaar_submodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] (s : Submodule ℝ E)
    (hs : s ≠ ⊤) : μ s = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨1 / 2, by simp, by norm_num⟩
  have A : IsBounded (range fun n : ℕ => c ^ n • x) :=
    have : Tendsto (fun n : ℕ => c ^ n • x) atTop (𝓝 ((0 : ℝ) • x)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one cpos.le cone).smul_const x
    isBounded_range_of_tendsto _ this
  apply addHaar_eq_zero_of_disjoint_translates μ _ A _
    (Submodule.closed_of_finiteDimensional s).measurableSet
  intro m n hmn
  simp only [Function.onFun, image_add_left, singleton_add, disjoint_left, mem_preimage,
    SetLike.mem_coe]
  intro y hym hyn
  have A : (c ^ n - c ^ m) • x ∈ s := by
    convert s.sub_mem hym hyn using 1
    simp only [sub_smul, neg_sub_neg, add_sub_add_right_eq_sub]
  have H : c ^ n - c ^ m ≠ 0 := by
    simpa only [sub_eq_zero, Ne] using (pow_right_strictAnti₀ cpos cone).injective.ne hmn.symm
  have : x ∈ s := by
    convert s.smul_mem (c ^ n - c ^ m)⁻¹ A
    rw [smul_smul, inv_mul_cancel₀ H, one_smul]
  exact hx this

theorem addHaar_affineSubspace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0 := by
  rcases s.eq_bot_or_nonempty with (rfl | hne)
  · rw [AffineSubspace.bot_coe, measure_empty]
  rw [Ne, ← AffineSubspace.direction_eq_top_iff_of_nonempty hne] at hs
  rcases hne with ⟨x, hx : x ∈ s⟩
  simpa only [AffineSubspace.coe_direction_eq_vsub_set_right hx, vsub_eq_sub, sub_eq_add_neg,
    image_add_right, neg_neg, measure_preimage_add_right] using addHaar_submodule μ s.direction hs

/-!
### Applying a linear map rescales Haar measure by the determinant

We first prove this on `ι → ℝ`, using that this is already known for the product Lebesgue
measure (thanks to matrices computations). Then, we extend this to any finite-dimensional real
vector space by using a linear equiv with a space of the form `ι → ℝ`, and arguing that such a
linear equiv maps Haar measure to Haar measure.
-/

-- DISSOLVED: map_linearMap_addHaar_pi_eq_smul_addHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

-- DISSOLVED: map_linearMap_addHaar_eq_smul_addHaar
