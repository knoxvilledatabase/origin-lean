/-
Extracted from LinearAlgebra/Vandermonde.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.
For each `CommRing R`, and function `v : Fin n → R` the matrix `vandermonde v`
is defined to be `Fin n` by `Fin n` matrix `V` whose `i`th row is `[1, (v i), (v i)^2, ...]`.
This matrix has determinant equal to the product of `v i - v j` over all unordered pairs `i,j`,
and therefore is nonsingular if and only if `v` is injective.

`vandermonde v` is a special case of two more general matrices we also define.
For a type `α` and functions `v w : α → R`, we write `rectVandermonde v w n` for
the `α × Fin n` matrix with `i`th row `[(w i) ^ (n-1), (v i) * (w i)^(n-2), ..., (v i)^(n-1)]`.
`projVandermonde v w = rectVandermonde v w n` is the square matrix case, where `α = Fin n`.
The determinant of `projVandermonde v w` is the product of `v j * w i - v i * w j`,
taken over all pairs `i,j` with `i < j`, which gives a similar characterization of
when it is nonsingular. Since `vandermonde v w = projVandermonde v 1`,
we can derive most of the API for the former in terms of the latter.

These extensions of Vandermonde matrices arise in the study of complete arcs in finite geometry,
coding theory, and representations of uniform matroids over finite fields.

## Main definitions

* `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.
* `rectVandermonde v w n`: an `α × Fin n` matrix whose
  `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.
* `projVandermonde v w`: a square matrix whose `i, j`-th entry is `(v i) ^ j * (w i) ^ (n-1-j)`.

## Main results

* `det_vandermonde`: `det (vandermonde v)` is the product of `v j - v i`, where
  `(i, j)` ranges over the set of pairs with `i < j`.
* `det_projVandermonde`: `det (projVandermonde v w)` is the product of `v j * w i - v i * w j`,
  taken over all pairs with `i < j`.

## Implementation notes

We derive the `det_vandermonde` formula from `det_projVandermonde`,
which is proved using an induction argument involving row operations and division.
To circumvent issues with non-invertible elements while still maintaining the generality of rings,
we first prove it for fields using the private lemma `det_projVandermonde_of_field`,
and then use an algebraic workaround to generalize to the ring case,
stating the strictly more general form as `det_projVandermonde`.

## TODO

Characterize when `rectVandermonde v w n` has linearly independent rows.
-/

variable {R K : Type*} [CommRing R] [Field K] {n : ℕ}

open Equiv Finset

open Matrix Fin

namespace Matrix

def rectVandermonde {α : Type*} (v w : α → R) (n : ℕ) : Matrix α (Fin n) R :=
  .of fun i j ↦ (v i) ^ j.1 * (w i) ^ j.rev.1

def projVandermonde (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  rectVandermonde v w n

def vandermonde (v : Fin n → R) : Matrix (Fin n) (Fin n) R := .of fun i j ↦ (v i) ^ j.1

lemma vandermonde_eq_projVandermonde (v : Fin n → R) : vandermonde v = projVandermonde v 1 := by
  simp [projVandermonde, rectVandermonde, vandermonde]
