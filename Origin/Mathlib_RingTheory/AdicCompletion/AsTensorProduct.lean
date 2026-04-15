/-
Extracted from RingTheory/AdicCompletion/AsTensorProduct.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show (in the `AdicCompletion` namespace):

- `ofTensorProduct_bijective_of_pi_of_fintype`: it is an isomorphism if `M = R^n`.
- `ofTensorProduct_surjective_of_finite`: it is surjective, if `M` is a finite `R`-module.
- `ofTensorProduct_bijective_of_finite_of_isNoetherian`: it is an isomorphism if `R` is Noetherian
  and `M` is a finite `R`-module.

As a corollary we obtain

- `flat_of_isNoetherian`: the adic completion of a Noetherian ring `R` is `R`-flat.

## TODO

- Show that `ofTensorProduct` is an isomorphism for any finite free `R`-module over an arbitrary
  ring. This is mostly composing with the isomorphism to `R^n` and checking that the diagram
  commutes.

-/

suppress_compilation

universe u v

variable {R : Type*} [CommRing R] (I : Ideal R)

variable (M : Type*) [AddCommGroup M] [Module R M]

variable {N : Type*} [AddCommGroup N] [Module R N]

open TensorProduct

namespace AdicCompletion

set_option backward.privateInPublic true in

private

def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    simp
