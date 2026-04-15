/-
Extracted from LinearAlgebra/TensorAlgebra/ToTensorPower.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `TensorAlgebra R M` is isomorphic to a direct sum of tensor powers, as
`TensorAlgebra.equivDirectSum`.
-/

open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

def toTensorAlgebra {n} : ⨂[R]^n M →ₗ[R] TensorAlgebra R M :=
  PiTensorProduct.lift (TensorAlgebra.tprod R M n)
