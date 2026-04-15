/-
Extracted from LinearAlgebra/TensorProduct/Associator.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Associators and unitors for tensor products of modules over a commutative ring.

-/

variable {R : Type*} [CommSemiring R]

variable {R' : Type*} [Monoid R']

variable {R'' : Type*} [Semiring R'']

variable {A M N P Q S T : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]

variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]

variable [DistribMulAction R' M]

variable [Module R'' M]

variable (M N)

namespace TensorProduct

variable [Module R P]

variable {M N}

variable (R M)

protected def lid : R ⊗[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinear (lift <| LinearMap.lsmul R M) (mk R R M 1) (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

end
