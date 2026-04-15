/-
Extracted from MeasureTheory/Measure/Lebesgue/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We show that the Lebesgue measure on the real line (constructed as a particular case of additive
Haar measure on inner product spaces) coincides with the Stieltjes measure associated
to the function `x ↦ x`. We deduce properties of this measure on `ℝ`, and then of the product
Lebesgue measure on `ℝⁿ`. In particular, we prove that they are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`, where they are proved more generally for any
additive Haar measure on a finite-dimensional real vector space.
-/

assert_not_exists MeasureTheory.integral

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/

namespace Real

variable {ι : Type*} [Fintype ι]

theorem volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure := by
  haveI : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
      Eq.symm <|
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis ℝ ℝ)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped, A]
  simp only [volume, Module.Basis.addHaar, one_smul]

theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]
