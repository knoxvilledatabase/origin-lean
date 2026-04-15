/-
Extracted from LinearAlgebra/TensorProduct/Pi.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Tensor product and products

In this file we examine the behaviour of the tensor product with arbitrary and finite products.

Let `S` be an `R`-algebra, `N` an `S`-module, `ι` an index type and `Mᵢ` a family of `R`-modules.
We then have a natural map

`TensorProduct.piRightHom`: `N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i`

In general, this is not an isomorphism, but if `ι` is finite, then it is
and it is packaged as `TensorProduct.piRight`. Also a special case for when `Mᵢ = R` is given.

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Prod.lean` for binary products.

-/

variable (R : Type*) [CommSemiring R]

variable (S : Type*) [CommSemiring S] [Algebra R S]

variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

variable (ι : Type*)

open LinearMap

namespace TensorProduct

variable {ι} (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

set_option backward.privateInPublic true in

private def piRightHomBil : N →ₗ[S] (∀ i, M i) →ₗ[R] ∀ i, N ⊗[R] M i where
  toFun n := LinearMap.pi (fun i ↦ mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := rfl

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def piRightHom : N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i :=
  AlgebraTensorModule.lift <| piRightHomBil R S N M
