/-
Extracted from Algebra/MvPolynomial/Comap.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `comap` operation on `MvPolynomial`

This file defines the `comap` function on `MvPolynomial`.

`MvPolynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

-/

namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R :=
  fun x i => aeval x (f (X i))
