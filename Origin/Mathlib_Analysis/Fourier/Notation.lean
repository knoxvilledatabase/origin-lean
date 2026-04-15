/-
Extracted from Analysis/Fourier/Notation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Type classes for the Fourier transform

In this file we define type classes for the Fourier transform and the inverse Fourier transform.
We introduce the notation `𝓕` and `𝓕⁻` in these classes to denote the Fourier transform and
the inverse Fourier transform, respectively.

Moreover, we provide type-classes that encode the linear structure and the Fourier inversion
theorem.
-/

universe u v w

variable {ι R E F : Type*}

class FourierTransform (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕 f` is the Fourier transform of `f`. The meaning of this notation is type-dependent. -/
  fourier : E → F

class FourierTransformInv (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕⁻ f` is the inverse Fourier transform of `f`. The meaning of this notation is
  type-dependent. -/
  fourierInv : E → F

namespace FourierTransform

export FourierTransformInv (fourierInv)
