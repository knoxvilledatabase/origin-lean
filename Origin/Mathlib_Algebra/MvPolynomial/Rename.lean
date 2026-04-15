/-
Extracted from Algebra/MvPolynomial/Rename.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `MvPolynomial.rename`
* `MvPolynomial.renameEquiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`.

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ α`

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)

theorem rename_C (f : σ → τ) (r : R) : rename f (C r) = C r :=
  eval₂_C _ _ _
