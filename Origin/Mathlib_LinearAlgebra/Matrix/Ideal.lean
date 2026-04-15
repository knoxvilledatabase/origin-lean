/-
Extracted from LinearAlgebra/Matrix/Ideal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals in a matrix ring

This file defines left (resp. two-sided) ideals in a matrix semiring (resp. ring)
over left (resp. two-sided) ideals in the base semiring (resp. ring).
We also characterize Jacobson radicals of ideals in such rings.

## Main results

* `TwoSidedIdeal.equivMatrix` and `TwoSidedIdeal.orderIsoMatrix`
  establish an order isomorphism between two-sided ideals in $R$ and those in $Mₙ(R)$.
* `TwoSidedIdeal.jacobson_matrix` shows that $J(Mₙ(I)) = Mₙ(J(I))$
  for any two-sided ideal $I ≤ R$.
-/

/-! ### Left ideals in a matrix semiring -/

namespace Ideal

open Matrix

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

def matrix (I : Ideal R) : Ideal (Matrix n n R) where
  __ := I.toAddSubmonoid.matrix
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul, mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)
