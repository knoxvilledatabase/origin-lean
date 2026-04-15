/-
Extracted from LinearAlgebra/TensorProduct/Submodule.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Some results on tensor product of submodules

## Linear maps induced by multiplication for submodules

Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`). We define some linear maps
induced by the multiplication in `S` (see also `LinearMap.mul'`), which are
mainly used in the definition of linearly disjointness (`Submodule.LinearDisjoint`).

- `Submodule.mulMap`: the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  induced by the multiplication in `S`, whose image is `M * N` (`Submodule.mulMap_range`).

- `Submodule.mulMap'`: the natural map `M ⊗[R] N →ₗ[R] M * N`
  induced by multiplication in `S`, which is surjective (`Submodule.mulMap'_surjective`).

- `Submodule.lTensorOne`, `Submodule.rTensorOne`: the natural isomorphism of `R`-modules between
  `i(R) ⊗[R] N` and `N`, resp. `M ⊗[R] i(R)` and `M`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `TensorProduct.lid`
  and `TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  Note that we use `⊥ : Subalgebra R S` instead of `1 : Submodule R S`, since the map
  `R →ₗ[R] (1 : Submodule R S)` is not defined directly in mathlib yet.

There are also `Submodule.mulLeftMap` and `Submodule.mulRightMap`, defined in earlier files.

-/

open scoped TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

def mulMap : M ⊗[R] N →ₗ[R] S := TensorProduct.lift ((LinearMap.mul R S).domRestrict₁₂ M N)
