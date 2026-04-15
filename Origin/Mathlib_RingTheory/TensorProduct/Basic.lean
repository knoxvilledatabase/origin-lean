/-
Extracted from RingTheory/TensorProduct/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The tensor product of R-algebras

This file provides results about the multiplicative structure on `A ⊗[R] B` when `R` is a
commutative (semi)ring and `A` and `B` are both `R`-algebras. On these tensor products,
multiplication is characterized by `(a₁ ⊗ₜ b₁) * (a₂ ⊗ₜ b₂) = (a₁ * a₂) ⊗ₜ (b₁ * b₂)`.

## Main declarations

- `Algebra.TensorProduct.semiring`: the ring structure on `A ⊗[R] B` for two `R`-algebras `A`, `B`.
- `Algebra.TensorProduct.leftAlgebra`: the `S`-algebra structure on `A ⊗[R] B`, for when `A` is
  additionally an `S` algebra.

## References

* [C. Kassel, *Quantum Groups* (§II.4)][Kassel1995]

-/

assert_not_exists Equiv.Perm.cycleType

open scoped TensorProduct

open TensorProduct

namespace LinearMap

section liftBaseChange

variable {R M N} (A) [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]

variable [AddCommMonoid N] [Module R M] [Module R N] [Module A N] [IsScalarTower R A N]

def liftBaseChangeEquiv : (M →ₗ[R] N) ≃ₗ[A] (A ⊗[R] M →ₗ[A] N) :=
  (LinearMap.ringLmapEquivSelf _ _ _).symm.trans (AlgebraTensorModule.lift.equiv _ _ _ _ _ _)

abbrev liftBaseChange (l : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] N :=
  LinearMap.liftBaseChangeEquiv A l
