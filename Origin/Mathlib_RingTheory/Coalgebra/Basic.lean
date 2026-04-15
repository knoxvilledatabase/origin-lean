/-
Extracted from RingTheory/Coalgebra/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coalgebras

In this file we define `Coalgebra`, and provide instances for:

* Commutative semirings: `CommSemiring.toCoalgebra`
* Binary products: `Prod.instCoalgebra`
* Finitely supported functions: `DFinsupp.instCoalgebra`, `Finsupp.instCoalgebra`
* Finite pi functions: `Pi.instCoalgebra`

## References

* <https://en.wikipedia.org/wiki/Coalgebra>
-/

universe u v w

open scoped TensorProduct

class CoalgebraStruct (R : Type u) (A : Type v)
    [CommSemiring R] [AddCommMonoid A] [Module R A] where
  /-- The comultiplication of the coalgebra -/
  comul : A →ₗ[R] A ⊗[R] A
  /-- The counit of the coalgebra -/
  counit : A →ₗ[R] R
