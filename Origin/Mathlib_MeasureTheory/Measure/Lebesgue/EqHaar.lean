/-
Extracted from MeasureTheory/Measure/Lebesgue/EqHaar.lean
Genuine: 32 | Conflates: 4 | Dissolved: 17 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Relationship between the Haar and Lebesgue measures

We prove that the Haar measure and Lebesgue measure are equal on `ℝ` and on `ℝ^ι`, in
`MeasureTheory.addHaarMeasure_eq_volume` and `MeasureTheory.addHaarMeasure_eq_volume_pi`.

We deduce basic properties of any Haar measure on a finite dimensional real vector space:
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

theorem Basis.parallelepiped_basisFun (ι : Type*) [Fintype ι] :
    (Pi.basisFun ℝ ι).parallelepiped = TopologicalSpace.PositiveCompacts.piIcc01 ι :=
  SetLike.coe_injective <| by
    refine Eq.trans ?_ ((uIcc_of_le ?_).trans (Set.pi_univ_Icc _ _).symm)
    · classical convert parallelepiped_single (ι := ι) 1
    · exact zero_le_one

theorem Basis.parallelepiped_eq_map  {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : Basis ι ℝ E) :
    b.parallelepiped = (PositiveCompacts.piIcc01 ι).map b.equivFun.symm
      b.equivFunL.symm.continuous b.equivFunL.symm.isOpenMap := by
  classical
  rw [← Basis.parallelepiped_basisFun, ← Basis.parallelepiped_map]
  congr with x
  simp [Pi.single_apply]

open MeasureTheory MeasureTheory.Measure

theorem Basis.map_addHaar {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]
    (b : Basis ι ℝ E) (f : E ≃L[ℝ] F) :
    map f b.addHaar = (b.map f.toLinearEquiv).addHaar := by
  have : IsAddHaarMeasure (map f b.addHaar) :=
    AddEquiv.isAddHaarMeasure_map b.addHaar f.toAddEquiv f.continuous f.symm.continuous
  rw [eq_comm, Basis.addHaar_eq_iff, Measure.map_apply f.continuous.measurable
    (PositiveCompacts.isCompact _).measurableSet, Basis.coe_parallelepiped, Basis.coe_map]
  erw [← image_parallelepiped, f.toEquiv.preimage_image, addHaar_self]

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

instance isAddHaarMeasure_volume_pi (ι : Type*) [Fintype ι] :
    IsAddHaarMeasure (volume : Measure (ι → ℝ)) :=
  inferInstance

namespace Measure

/-!
### Strict subspaces have zero measure
-/

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
  obtain ⟨c, cpos, cone⟩ : ∃ c : ℝ, 0 < c ∧ c < 1 := ⟨1 / 2, by norm_num, by norm_num⟩
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

-- DISSOLVED: addHaar_preimage_linearMap

-- DISSOLVED: addHaar_preimage_continuousLinearMap

@[simp]
theorem addHaar_preimage_linearEquiv (f : E ≃ₗ[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s := by
  have A : LinearMap.det (f : E →ₗ[ℝ] E) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  convert addHaar_preimage_linearMap μ A s
  simp only [LinearEquiv.det_coe_symm]

@[simp]
theorem addHaar_preimage_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f ⁻¹' s) = ENNReal.ofReal |LinearMap.det (f.symm : E →ₗ[ℝ] E)| * μ s :=
  addHaar_preimage_linearEquiv μ _ s

@[simp]
theorem addHaar_image_linearMap (f : E →ₗ[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det f| * μ s := by
  rcases ne_or_eq (LinearMap.det f) 0 with (hf | hf)
  · let g := (f.equivOfDetNeZero hf).toContinuousLinearEquiv
    change μ (g '' s) = _
    rw [ContinuousLinearEquiv.image_eq_preimage g s, addHaar_preimage_continuousLinearEquiv]
    congr
  · simp only [hf, zero_mul, ENNReal.ofReal_zero, abs_zero]
    have : μ (LinearMap.range f) = 0 :=
      addHaar_submodule μ _ (LinearMap.range_lt_top_of_det_eq_zero hf).ne
    exact le_antisymm (le_trans (measure_mono (image_subset_range _ _)) this.le) (zero_le _)

@[simp]
theorem addHaar_image_continuousLinearMap (f : E →L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  addHaar_image_linearMap μ _ s

@[simp]
theorem addHaar_image_continuousLinearEquiv (f : E ≃L[ℝ] E) (s : Set E) :
    μ (f '' s) = ENNReal.ofReal |LinearMap.det (f : E →ₗ[ℝ] E)| * μ s :=
  μ.addHaar_image_linearMap (f : E →ₗ[ℝ] E) s

-- DISSOLVED: LinearMap.quasiMeasurePreserving

-- DISSOLVED: ContinuousLinearMap.quasiMeasurePreserving

/-!
### Basic properties of Haar measures on real vector spaces
-/

-- DISSOLVED: map_addHaar_smul

-- DISSOLVED: quasiMeasurePreserving_smul

-- DISSOLVED: addHaar_preimage_smul

@[simp]
theorem addHaar_smul (r : ℝ) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
  rcases ne_or_eq r 0 with (h | rfl)
  · rw [← preimage_smul_inv₀ h, addHaar_preimage_smul μ (inv_ne_zero h), inv_pow, inv_inv]
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · simp only [measure_empty, mul_zero, smul_set_empty]
  rw [zero_smul_set hs, ← singleton_zero]
  by_cases h : finrank ℝ E = 0
  · haveI : Subsingleton E := finrank_zero_iff.1 h
    simp only [h, one_mul, ENNReal.ofReal_one, abs_one, Subsingleton.eq_univ_of_nonempty hs,
      pow_zero, Subsingleton.eq_univ_of_nonempty (singleton_nonempty (0 : E))]
  · haveI : Nontrivial E := nontrivial_of_finrank_pos (bot_lt_iff_ne_bot.2 h)
    simp only [h, zero_mul, ENNReal.ofReal_zero, abs_zero, Ne, not_false_iff,
      zero_pow, measure_singleton]

theorem addHaar_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (s : Set E) :
    μ (r • s) = ENNReal.ofReal (r ^ finrank ℝ E) * μ s := by
  rw [addHaar_smul, abs_pow, abs_of_nonneg hr]

variable {μ} {s : Set E}

theorem NullMeasurableSet.const_smul (hs : NullMeasurableSet s μ) (r : ℝ) :
    NullMeasurableSet (r • s) μ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simpa [zero_smul_set hs'] using nullMeasurableSet_singleton _
  obtain ⟨t, ht, hst⟩ := hs
  refine ⟨_, ht.const_smul_of_ne_zero hr, ?_⟩
  rw [← measure_symmDiff_eq_zero_iff] at hst ⊢
  rw [← smul_set_symmDiff₀ hr, addHaar_smul μ, hst, mul_zero]

variable (μ)

@[simp]
theorem addHaar_image_homothety (x : E) (r : ℝ) (s : Set E) :
    μ (AffineMap.homothety x r '' s) = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s :=
  calc
    μ (AffineMap.homothety x r '' s) = μ ((fun y => y + x) '' (r • (fun y => y + -x) '' s)) := by
      simp only [← image_smul, image_image, ← sub_eq_add_neg]; rfl
    _ = ENNReal.ofReal (abs (r ^ finrank ℝ E)) * μ s := by
      simp only [image_add_right, measure_preimage_add_right, addHaar_smul]

/-! We don't need to state `map_addHaar_neg` here, because it has already been proved for
general Haar measures on general commutative groups. -/

/-! ### Measure of balls -/

theorem addHaar_ball_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) : μ (ball x r) = μ (ball (0 : E) r) := by
  have : ball (0 : E) r = (x + ·) ⁻¹' ball x r := by simp [preimage_add_ball]
  rw [this, measure_preimage_add]

theorem addHaar_closedBall_center {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (closedBall (0 : E) r) := by
  have : closedBall (0 : E) r = (x + ·) ⁻¹' closedBall x r := by simp [preimage_add_closedBall]
  rw [this, measure_preimage_add]

theorem addHaar_ball_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  have : ball (0 : E) (r * s) = r • ball (0 : E) s := by
    simp only [_root_.smul_ball hr.ne' (0 : E) s, Real.norm_eq_abs, abs_of_nonneg hr.le, smul_zero]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_ball_center, abs_pow]

theorem addHaar_ball_of_pos (x : E) {r : ℝ} (hr : 0 < r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul_of_pos μ x hr, mul_one]

-- CONFLATES (assumes ground = zero): addHaar_ball_mul
theorem addHaar_ball_mul [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    μ (ball x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 s) := by
  rcases hr.eq_or_lt with (rfl | h)
  · simp only [zero_pow (finrank_pos (R := ℝ) (M := E)).ne', measure_empty, zero_mul,
      ENNReal.ofReal_zero, ball_zero]
  · exact addHaar_ball_mul_of_pos μ x h s

-- CONFLATES (assumes ground = zero): addHaar_ball
theorem addHaar_ball [Nontrivial E] (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (ball x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [← addHaar_ball_mul μ x hr, mul_one]

theorem addHaar_closedBall_mul_of_pos (x : E) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall' hr.ne' (0 : E), abs_of_nonneg hr.le]
  simp only [this, addHaar_smul, abs_of_nonneg hr.le, addHaar_closedBall_center, abs_pow]

theorem addHaar_closedBall_mul (x : E) {r : ℝ} (hr : 0 ≤ r) {s : ℝ} (hs : 0 ≤ s) :
    μ (closedBall x (r * s)) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 s) := by
  have : closedBall (0 : E) (r * s) = r • closedBall (0 : E) s := by
    simp [smul_closedBall r (0 : E) hs, abs_of_nonneg hr]
  simp only [this, addHaar_smul, abs_of_nonneg hr, addHaar_closedBall_center, abs_pow]

theorem addHaar_closedBall' (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall 0 1) := by
  rw [← addHaar_closedBall_mul μ x hr zero_le_one, mul_one]

theorem addHaar_closed_unit_ball_eq_addHaar_unit_ball :
    μ (closedBall (0 : E) 1) = μ (ball 0 1) := by
  apply le_antisymm _ (measure_mono ball_subset_closedBall)
  have A : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ finrank ℝ E) * μ (closedBall (0 : E) 1)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal ((1 : ℝ) ^ finrank ℝ E) * μ (closedBall (0 : E) 1))) := by
    refine ENNReal.Tendsto.mul ?_ (by simp) tendsto_const_nhds (by simp)
    exact ENNReal.tendsto_ofReal ((tendsto_id'.2 nhdsWithin_le_nhds).pow _)
  simp only [one_pow, one_mul, ENNReal.ofReal_one] at A
  refine le_of_tendsto A ?_
  refine mem_nhdsWithin_Iio_iff_exists_Ioo_subset.2 ⟨(0 : ℝ), by simp, fun r hr => ?_⟩
  dsimp
  rw [← addHaar_closedBall' μ (0 : E) hr.1.le]
  exact measure_mono (closedBall_subset_ball hr.2)

theorem addHaar_closedBall (x : E) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall x r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) := by
  rw [addHaar_closedBall' μ x hr, addHaar_closed_unit_ball_eq_addHaar_unit_ball]

-- CONFLATES (assumes ground = zero): addHaar_closedBall_eq_addHaar_ball
theorem addHaar_closedBall_eq_addHaar_ball [Nontrivial E] (x : E) (r : ℝ) :
    μ (closedBall x r) = μ (ball x r) := by
  by_cases h : r < 0
  · rw [Metric.closedBall_eq_empty.mpr h, Metric.ball_eq_empty.mpr h.le]
  push_neg at h
  rw [addHaar_closedBall μ x h, addHaar_ball μ x h]

-- DISSOLVED: addHaar_sphere_of_ne_zero

-- CONFLATES (assumes ground = zero): addHaar_sphere
theorem addHaar_sphere [Nontrivial E] (x : E) (r : ℝ) : μ (sphere x r) = 0 := by
  rcases eq_or_ne r 0 with (rfl | h)
  · rw [sphere_zero, measure_singleton]
  · exact addHaar_sphere_of_ne_zero μ x h

-- DISSOLVED: addHaar_singleton_add_smul_div_singleton_add_smul

instance (priority := 100) isUnifLocDoublingMeasureOfIsAddHaarMeasure :
    IsUnifLocDoublingMeasure μ := by
  refine ⟨⟨(2 : ℝ≥0) ^ finrank ℝ E, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin] with r hr x
  rw [addHaar_closedBall_mul μ x zero_le_two (le_of_lt hr), addHaar_closedBall_center μ x,
    ENNReal.ofReal, Real.toNNReal_pow zero_le_two]
  simp only [Real.toNNReal_ofNat, le_refl]

section

/-!
### The Lebesgue measure associated to an alternating map
-/

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem addHaar_parallelepiped (b : Basis ι ℝ G) (v : ι → G) :
    b.addHaar (parallelepiped v) = ENNReal.ofReal |b.det v| := by
  have : FiniteDimensional ℝ G := FiniteDimensional.of_fintype_basis b
  have A : parallelepiped v = b.constr ℕ v '' parallelepiped b := by
    rw [image_parallelepiped]
    -- Porting note: was `congr 1 with i` but Lean 4 `congr` applies `ext` first
    refine congr_arg _ <| funext fun i ↦ ?_
    exact (b.constr_basis ℕ v i).symm
  rw [A, addHaar_image_linearMap, b.addHaar_self, mul_one, ← LinearMap.det_toMatrix b,
    ← Basis.toMatrix_eq_toMatrix_constr, Basis.det_apply]

variable [FiniteDimensional ℝ G] {n : ℕ} [_i : Fact (finrank ℝ G = n)]

noncomputable irreducible_def _root_.AlternatingMap.measure (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) :
    Measure G :=
  ‖ω (finBasisOfFinrankEq ℝ G _i.out)‖₊ • (finBasisOfFinrankEq ℝ G _i.out).addHaar

theorem _root_.AlternatingMap.measure_parallelepiped (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ)
    (v : Fin n → G) : ω.measure (parallelepiped v) = ENNReal.ofReal |ω v| := by
  conv_rhs => rw [ω.eq_smul_basis_det (finBasisOfFinrankEq ℝ G _i.out)]
  simp only [addHaar_parallelepiped, AlternatingMap.measure, coe_nnreal_smul_apply,
    AlternatingMap.smul_apply, Algebra.id.smul_eq_mul, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    Real.ennnorm_eq_ofReal_abs]

instance (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) : IsAddLeftInvariant ω.measure := by
  rw [AlternatingMap.measure]; infer_instance

instance (ω : G [⋀^Fin n]→ₗ[ℝ] ℝ) : IsLocallyFiniteMeasure ω.measure := by
  rw [AlternatingMap.measure]; infer_instance

end

/-!
### Density points

Besicovitch covering theorem ensures that, for any locally finite measure on a finite-dimensional
real vector space, almost every point of a set `s` is a density point, i.e.,
`μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as `r` tends to `0`
(see `Besicovitch.ae_tendsto_measure_inter_div`).
When `μ` is a Haar measure, one can deduce the same property for any rescaling sequence of sets,
of the form `{x} + r • t` where `t` is a set with positive finite measure, instead of the sequence
of closed balls.

We argue first for the dual property, i.e., if `s` has density `0` at `x`, then
`μ (s ∩ ({x} + r • t)) / μ ({x} + r • t)` tends to `0`. First when `t` is contained in the ball
of radius `1`, in `tendsto_addHaar_inter_smul_zero_of_density_zero_aux1`,
(by arguing by inclusion). Then when `t` is bounded, reducing to the previous one by rescaling, in
`tendsto_addHaar_inter_smul_zero_of_density_zero_aux2`.
Then for a general set `t`, by cutting it into a bounded part and a part with small measure, in
`tendsto_addHaar_inter_smul_zero_of_density_zero`.
Going to the complement, one obtains the desired property at points of density `1`, first when
`s` is measurable in `tendsto_addHaar_inter_smul_one_of_density_one_aux`, and then without this
assumption in `tendsto_addHaar_inter_smul_one_of_density_one` by applying the previous lemma to
the measurable hull `toMeasurable μ s`
-/

-- DISSOLVED: tendsto_addHaar_inter_smul_zero_of_density_zero_aux1

-- DISSOLVED: tendsto_addHaar_inter_smul_zero_of_density_zero_aux2

-- DISSOLVED: tendsto_addHaar_inter_smul_zero_of_density_zero

-- DISSOLVED: tendsto_addHaar_inter_smul_one_of_density_one_aux

-- DISSOLVED: tendsto_addHaar_inter_smul_one_of_density_one

-- DISSOLVED: eventually_nonempty_inter_smul_of_density_one

end Measure

end MeasureTheory
