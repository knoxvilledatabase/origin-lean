/-
Extracted from Analysis/Distribution/SchwartzSpace/Fourier.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.

## Main statements
* `SchwartzMap.fderivCLM_fourier_eq`: The derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • innerSL ℝ`.
* `SchwartzMap.lineDerivOp_fourier_eq`: The line derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
* `SchwartzMap.integral_bilin_fourier_eq`: The Fourier transform is self-adjoint.
* `SchwartzMap.integral_inner_fourier_fourier`: Plancherel's theorem for Schwartz functions.

-/

open Real MeasureTheory MeasureTheory.Measure

open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section definition

def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM ((𝓕 : (V → E) → (V → E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f ↦ contDiff_fourier (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2, by positivity,
      fun f x ↦ ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn ↦ integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ ≤ ∑ _ ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) ∈ Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) ∈ Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]

-- INSTANCE (free from Core): instFourierTransform

-- INSTANCE (free from Core): instFourierAdd

-- INSTANCE (free from Core): instFourierSMul

-- INSTANCE (free from Core): instContinuousFourier
