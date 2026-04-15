/-
Extracted from Data/Matrix/Diagonal.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Diagonal matrices

This file defines diagonal matrices and the `AddCommMonoidWithOne` structure on matrices.

## Main definitions

* `Matrix.diagonal d`: matrix with the vector `d` along the diagonal
* `Matrix.diag M`: the diagonal of a square matrix
* `Matrix.instAddCommMonoidWithOne`: matrices are an additive commutative monoid with one
-/

assert_not_exists Algebra TrivialStar

universe u u' v w

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

namespace Matrix

section Diagonal

variable [DecidableEq n]

def diagonal [Zero α] (d : n → α) : Matrix n n α :=
  of fun i j => if i = j then d i else 0
