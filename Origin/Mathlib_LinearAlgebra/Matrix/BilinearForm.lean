/-
Extracted from LinearAlgebra/Matrix/BilinearForm.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bilinear form

This file defines the conversion between bilinear forms and matrices.

## Main definitions

* `Matrix.toBilin` given a basis define a bilinear form
* `Matrix.toBilin'` define the bilinear form on `n → R`
* `BilinForm.toMatrix`: calculate the matrix coefficients of a bilinear form
* `BilinForm.toMatrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notation

In this file we use the following type variables:
- `M₁` is a module over the commutative semiring `R₁`,
- `M₂` is a module over the commutative ring `R₂`.

## Tags

bilinear form, bilin form, BilinearForm, matrix, basis

-/

open LinearMap (BilinForm)

open Module

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]

variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

section Matrix

variable {n o : Type*}

open Finset LinearMap Matrix

open Matrix

def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₁) : BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M

theorem Matrix.toBilin'Aux_single [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n) :
    M.toBilin'Aux (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ _ _ _

def LinearMap.BilinForm.toMatrixAux (b : n → M₁) : BilinForm R₁ M₁ →ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂Aux R₁ b b
