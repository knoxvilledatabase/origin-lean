/-
Extracted from LinearAlgebra/Contraction.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Contractions

Given modules $M, N$ over a commutative ring $R$, this file defines the natural linear maps:
$M^* \otimes M \to R$, $M \otimes M^* \to R$, and $M^* \otimes N → Hom(M, N)$, as well as proving
some basic properties of these maps.

## Tags

contraction, dual module, tensor product
-/

variable {ι : Type*} (R M N P Q : Type*)

attribute [local ext high] TensorProduct.ext

section Contraction

open TensorProduct LinearMap Matrix Module

open TensorProduct

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q]

variable [Module R M] [Module R N] [Module R P] [Module R Q]

variable [DecidableEq ι] [Fintype ι] (b : Basis ι R M)

def contractLeft : Module.Dual R M ⊗[R] M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun LinearMap.id

def contractRight : M ⊗[R] Module.Dual R M →ₗ[R] R :=
  (uncurry _ _ _ _).toFun (LinearMap.flip LinearMap.id)

def dualTensorHom : Module.Dual R M ⊗[R] N →ₗ[R] M →ₗ[R] N :=
  let M' := Module.Dual R M
  (uncurry (.id R) M' N (M →ₗ[R] N) : _ → M' ⊗ N →ₗ[R] M →ₗ[R] N) LinearMap.smulRightₗ

variable {R M N P Q}
