/-
Extracted from LinearAlgebra/Complex/Orientation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The standard orientation on `ℂ`.

This had previously been in `LinearAlgebra.Orientation`,
but keeping it separate results in a significant import reduction.
-/

namespace Complex

protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.orientation

end Complex
