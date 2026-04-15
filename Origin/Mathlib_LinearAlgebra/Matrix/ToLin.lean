/-
Extracted from LinearAlgebra/Matrix/ToLin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `LinearMap.toMatrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
  the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `Matrix κ ι R`
* `Matrix.toLin`: the inverse of `LinearMap.toMatrix`
* `LinearMap.toMatrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
  to `Matrix m n R` (with the standard basis on `m → R` and `n → R`)
* `Matrix.toLin'`: the inverse of `LinearMap.toMatrix'`
* `algEquivMatrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
  `R`-endomorphisms of `M` and `Matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `Matrix.mulVec` gives us a linear equivalence
`Matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `Matrix.vecMul` gives us a linear equivalence
`Matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `Matrix.vecMul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/

noncomputable section

open LinearMap Matrix Module Set Submodule

/-!
### Bilinear versions of matrix products

The definitions in this section are stated with two extra rings, to allow for non-commutative rings.
-/

section Bilinear

variable {l m n R S A : Type*}

variable [Semiring R] [Semiring S] [NonUnitalNonAssocSemiring A]

variable [Module R A] [Module S A]

variable [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

variable (R S)

def Matrix.vecMulBilin [Fintype m] : (m → A) →ₗ[R] Matrix m n A →ₗ[S] (n → A) where
  toFun x :=
  { toFun M := x ᵥ* M
    map_add' _ _ := vecMul_add _ _ _
    map_smul' _ _ := vecMul_smul _ _ _ }
  map_add' _ _ := LinearMap.ext fun _ => add_vecMul _ _ _
  map_smul' _ _ := LinearMap.ext fun _ => smul_vecMul _ _ _
