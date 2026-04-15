/-
Extracted from LinearAlgebra/Matrix/Kronecker.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `Matrix.kroneckerMap`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kroneckerMap f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `Matrix.kroneckerMapBilinear`: when `f` is bilinear, so is `kroneckerMap f`.

## Specializations

* `Matrix.kronecker`: An alias of `kroneckerMap (*)`. Prefer using the notation.
* `Matrix.kroneckerBilinear`: `Matrix.kronecker` is bilinear

* `Matrix.kroneckerTMul`: An alias of `kroneckerMap (⊗ₜ)`. Prefer using the notation.
* `Matrix.kroneckerTMulBilinear`: `Matrix.kroneckerTMul` is bilinear

## Notation

These require `open Kronecker`:

* `A ⊗ₖ B` for `kroneckerMap (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kroneckerMap (⊗ₜ) A B`.
  Lemmas about this notation use the token `kroneckerTMul`.

-/

namespace Matrix

open scoped RightActions

variable {R S α α' β β' γ γ' : Type*}

variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

section KroneckerMap

def kroneckerMap (f : α → β → γ) (A : Matrix l m α) (B : Matrix n p β) : Matrix (l × n) (m × p) γ :=
  of fun (i : l × n) (j : m × p) => f (A i.1 j.1) (B i.2 j.2)
