/-
Extracted from LinearAlgebra/Matrix/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Matrices

This file defines basic properties of matrices up to the module structure.

Matrices with rows indexed by `m`, columns indexed by `n`, and entries of type `α` are represented
with `Matrix m n α`. For the typical approach of counting rows and columns,
`Matrix (Fin m) (Fin n) α` can be used.

## Main definitions

* `Matrix.transpose`: transpose of a matrix, turning rows into columns and vice versa
* `Matrix.submatrix`: take a submatrix by reindexing rows and columns
* `Matrix.module`: matrices are a module over the ring of entries
* `Set.matrix`: set of matrices with entries in a given set

## Notation

The scope `Matrix` gives the following notation:

* `ᵀ` for `Matrix.transpose`

See `Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean` for

* `ᴴ` for `Matrix.conjTranspose`

## Implementation notes

For convenience, `Matrix m n α` is defined as `m → n → α`, as this allows elements of the matrix
to be accessed with `A i j`. However, it is not advisable to _construct_ matrices using terms of the
form `fun i j ↦ _` or even `(fun i j ↦ _ : Matrix m n α)`, as these are not recognized by Lean
as having the right type. Instead, `Matrix.of` should be used.
-/

assert_not_exists Algebra TrivialStar

universe u u' v w

def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Ext

variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
  ⟨fun h => funext fun i => funext <| h i, fun h => by simp [h]⟩
