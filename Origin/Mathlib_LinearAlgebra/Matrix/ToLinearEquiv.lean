/-
Extracted from LinearAlgebra/Matrix/ToLinearEquiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices and linear equivalences

This file gives the map `Matrix.toLinearEquiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

* `Matrix.toLinearEquiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

* `Matrix.exists_mulVec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear equivalence, linear isomorphism, determinant, inverse

-/

open Module

variable {n : Type*} [Fintype n]

namespace Matrix

section LinearEquiv

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

section ToLinearEquiv'

variable [DecidableEq n]

def toLinearEquiv' (P : Matrix n n R) (_ : Invertible P) : (n → R) ≃ₗ[R] n → R :=
  GeneralLinearGroup.generalLinearEquiv _ _ <|
    Matrix.GeneralLinearGroup.toLin <| unitOfInvertible P
