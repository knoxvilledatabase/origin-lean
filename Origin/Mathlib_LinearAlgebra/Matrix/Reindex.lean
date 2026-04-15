/-
Extracted from LinearAlgebra/Matrix/Reindex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Changing the index type of a matrix

This file concerns the map `Matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `Matrix.reindexLinearEquiv R A`: `Matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `Matrix.reindexAlgEquiv R`: `Matrix.reindex` is an `R`-algebra equivalence between `R`-matrices.

## Tags

matrix, reindex

-/

namespace Matrix

open Equiv Matrix

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}

variable (R A : Type*)

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A where
  __ := reindex eₘ eₙ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
