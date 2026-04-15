/-
Extracted from Algebra/Algebra/Tower.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebras.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the latter asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `toAlgHom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/

open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]

variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

variable {A}

def lsmul : A →ₐ[R] Module.End B M where
  toFun := DistribSMul.toLinearMap B M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' a b := LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' _a _b := LinearMap.ext fun _ => add_smul _ _ _
  commutes' r := LinearMap.ext <| algebraMap_smul A r
