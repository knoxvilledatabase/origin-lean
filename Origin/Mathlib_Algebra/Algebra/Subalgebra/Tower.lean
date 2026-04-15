/-
Extracted from Algebra/Algebra/Subalgebra/Tower.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Subalgebras in towers of algebras

In this file we prove facts about subalgebras in towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

## Main results

* `IsScalarTower.Subalgebra`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S/S₀` is a tower
* `IsScalarTower.Subalgebra'`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S₀/R` is a tower
* `Subalgebra.restrictScalars`: turn an `S`-subalgebra of `A` into an `R`-subalgebra of `A`,
  given that `A/S/R` is a tower

-/

open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {A}

theorem lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x :=
  Eq.symm <| LinearMap.ext <| smul_def x

end Algebra

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A]

variable [Algebra R S] [Algebra S A]

-- INSTANCE (free from Core): subalgebra

variable [Algebra R A] [IsScalarTower R S A]

-- INSTANCE (free from Core): subalgebra'

end Semiring

end IsScalarTower

namespace Subalgebra

open IsScalarTower

section Semiring

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebraMap_mem' := fun x ↦ by
      rw [IsScalarTower.algebraMap_apply R S A]
      exact U.algebraMap_mem _ }
