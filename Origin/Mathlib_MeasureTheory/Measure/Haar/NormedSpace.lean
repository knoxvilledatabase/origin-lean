/-
Extracted from MeasureTheory/Measure/Haar/NormedSpace.lean
Genuine: 12 | Conflates: 0 | Dissolved: 9 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Basic properties of Haar measures on real vector spaces

-/

noncomputable section

open scoped NNReal ENNReal Pointwise Topology

open Inv Set Function MeasureTheory.Measure Filter

open Module

namespace MeasureTheory

namespace Measure

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] : NoAtoms μ := by
  infer_instance

section LinearEquiv

variable {𝕜 G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [TopologicalAddGroup G] [TopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H]
  [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H] [T2Space H]

instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) : IsAddHaarMeasure (μ.map e) :=
  e.toContinuousLinearEquiv.isAddHaarMeasure_map _

end LinearEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem integral_comp_smul (f : E → F) (R : ℝ) :
    ∫ x, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR)
  · simp only [zero_smul, integral_const]
    rcases Nat.eq_zero_or_pos (finrank ℝ E) with (hE | hE)
    · have : Subsingleton E := finrank_zero_iff.1 hE
      have : f = fun _ => f 0 := by ext x; rw [Subsingleton.elim x 0]
      conv_rhs => rw [this]
      simp only [hE, pow_zero, inv_one, abs_one, one_smul, integral_const]
    · have : Nontrivial E := finrank_pos_iff.1 hE
      simp only [zero_pow hE.ne', measure_univ_of_isAddLeftInvariant, ENNReal.top_toReal, zero_smul,
        inv_zero, abs_zero]
  · calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂Measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hR).unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]

theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ) {hR : 0 ≤ R} :
    ∫ x, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R, abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR _))]

theorem integral_comp_inv_smul (f : E → F) (R : ℝ) :
    ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R⁻¹, inv_pow, inv_inv]

theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x, f (R⁻¹ • x) ∂μ = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R, abs_of_nonneg (pow_nonneg hR _)]

-- DISSOLVED: setIntegral_comp_smul

alias set_integral_comp_smul := setIntegral_comp_smul

theorem setIntegral_comp_smul_of_pos (f : E → F) {R : ℝ} (s : Set E) (hR : 0 < R) :
    ∫ x in s, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x in R • s, f x ∂μ := by
  rw [setIntegral_comp_smul μ f s hR.ne', abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]

alias set_integral_comp_smul_of_pos := setIntegral_comp_smul_of_pos

theorem integral_comp_mul_left (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (a * x)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_smul, Module.finrank_self, pow_one]

theorem integral_comp_inv_mul_left (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (a⁻¹ * x)) = |a| • ∫ y : ℝ, g y := by
  simp_rw [← smul_eq_mul, Measure.integral_comp_inv_smul, Module.finrank_self, pow_one]

theorem integral_comp_mul_right (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (x * a)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_mul_left g a

theorem integral_comp_inv_mul_right (g : ℝ → F) (a : ℝ) :
    (∫ x : ℝ, g (x * a⁻¹)) = |a| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a

theorem integral_comp_div (g : ℝ → F) (a : ℝ) : (∫ x : ℝ, g (x / a)) = |a| • ∫ y : ℝ, g y :=
  integral_comp_inv_mul_right g a

end Measure

variable {F : Type*} [NormedAddCommGroup F]

-- DISSOLVED: integrable_comp_smul_iff

-- DISSOLVED: Integrable.comp_smul

-- DISSOLVED: integrable_comp_mul_left_iff

-- DISSOLVED: Integrable.comp_mul_left'

-- DISSOLVED: integrable_comp_mul_right_iff

-- DISSOLVED: Integrable.comp_mul_right'

-- DISSOLVED: integrable_comp_div_iff

-- DISSOLVED: Integrable.comp_div

section InnerProductSpace

variable {E' F' A : Type*}

variable [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']

variable [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  [MeasurableSpace F'] [BorelSpace F']

variable (f : E' ≃ₗᵢ[ℝ] F')

variable [NormedAddCommGroup A]

theorem integrable_comp (g : F' → A) : Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasureEquiv.measurableEmbedding

theorem integral_comp [NormedSpace ℝ A] (g : F' → A) : ∫ (x : E'), g (f x) = ∫ (y : F'), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasureEquiv) g

end InnerProductSpace

end MeasureTheory
