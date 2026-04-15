/-
Extracted from Analysis/Fourier/LpSpace.lean
Genuine: 1 of 11 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!

# The Fourier transform on $L^p$

In this file we define the Fourier transform on $L^2$ as a linear isometry equivalence.

## Main definitions

* `MeasureTheory.Lp.fourierTransformₗᵢ`: The Fourier transform on $L^2$ as a linear isometry
  equivalence.

## Main statements

* `SchwartzMap.toLp_fourier_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
  transform on $L^2$.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`: The Fourier transform on $L^2$ agrees with
  the Fourier transform on `𝓢'(E, F)`.

-/

noncomputable section

section FourierTransform

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace MeasureTheory.Lp

variable (E F) in

def fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) :=
  (fourierEquiv ℂ 𝓢(E, F)).extendOfIsometry
    (toLpCLM ℂ (E := E) F 2 volume) (toLpCLM ℂ (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toL2_eq

-- INSTANCE (free from Core): instFourierTransform

-- INSTANCE (free from Core): instFourierAdd

-- INSTANCE (free from Core): instFourierSMul

-- INSTANCE (free from Core): instContinuousFourier

-- INSTANCE (free from Core): instFourierTransformInv

-- INSTANCE (free from Core): instFourierInvAdd

-- INSTANCE (free from Core): instFourierInvSMul

-- INSTANCE (free from Core): instContinuousFourierInv

-- INSTANCE (free from Core): instFourierPair

-- INSTANCE (free from Core): instFourierPairInv
