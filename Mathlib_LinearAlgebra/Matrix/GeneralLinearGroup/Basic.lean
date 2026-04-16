/-
Extracted from LinearAlgebra/Matrix/GeneralLinearGroup/Basic.lean
Genuine: 1 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

noncomputable section

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

namespace Matrix

section Examples

@[simps! (config := .asFn) val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)

end Examples

end Matrix
