/-
Extracted from MeasureTheory/Measure/Haar/InnerProductSpace.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Volume forms and measures on inner product spaces

A volume form induces a Lebesgue measure on general finite-dimensional real vector spaces. In this
file, we discuss the specific situation of inner product spaces, where an orientation gives
rise to a canonical volume form. We show that the measure coming from this volume form gives
measure `1` to the parallelepiped spanned by any orthonormal basis, and that it coincides with
the canonical `volume` from the `MeasureSpace` instance.
-/

open Module MeasureTheory MeasureTheory.Measure Set WithLp

variable {ι E F : Type*}

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[ℝ] F)

def toMeasurableEquiv : E ≃ᵐ F := f.toHomeomorph.toMeasurableEquiv
