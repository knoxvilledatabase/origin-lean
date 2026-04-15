/-
Extracted from Algebra/Central/Matrix.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The matrix algebra is a central algebra
-/

namespace Matrix

variable {n R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype n] [DecidableEq n]

theorem subalgebraCenter_eq_scalarAlgHom_map :
    Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (scalarAlgHom n R) :=
  SetLike.coe_injective center_eq_scalar_image

end Matrix

namespace Algebra.IsCentral

variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D] [IsCentral K D]

open Matrix in

-- INSTANCE (free from Core): matrix

end Algebra.IsCentral
