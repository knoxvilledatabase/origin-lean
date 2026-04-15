/-
Extracted from Algebra/MvPolynomial/Basic.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Multivariate polynomials

This file defines polynomial rings over a base ring (or even semiring),
with variables from a general type `σ` (which could be infinite).

## Important definitions

Let `R` be a commutative ring (or a semiring) and let `σ` be an arbitrary
type. This file creates the type `MvPolynomial σ R`, which mathematicians
might denote $R[X_i : i \in σ]$. It is the type of multivariate
(a.k.a. multivariable) polynomials, with variables
corresponding to the terms in `σ`, and coefficients in `R`.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `MvPolynomial σ R` : the type of polynomials with variables of type `σ` and coefficients
  in the commutative semiring `R`
* `monomial s a` : the monomial which mathematically would be denoted `a * X^s`
* `C a` : the constant polynomial with value `a`
* `X i` : the degree one monomial corresponding to i; mathematically this might be denoted `Xᵢ`.
* `coeff s p` : the coefficient of `s` in `p`.

## Implementation notes

Recall that if `Y` has a zero, then `X →₀ Y` is the type of functions from `X` to `Y` with finite
support, i.e. such that only finitely many elements of `X` get sent to non-zero terms in `Y`.
The definition of `MvPolynomial σ R` is `(σ →₀ ℕ) →₀ R`; here `σ →₀ ℕ` denotes the space of all
monomials in the variables, and the function to `R` sends a monomial to its coefficient in
the polynomial being represented.

## Tags

polynomial, multivariate polynomial, multivariable polynomial

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

abbrev MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=
  AddMonoidAlgebra R (σ →₀ ℕ)

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

def monomial (s : σ →₀ ℕ) : R →ₗ[R] MvPolynomial σ R :=
  AddMonoidAlgebra.lsingle s

theorem mul_def : p * q = p.sum fun m a => q.sum fun n b => monomial (m + n) (a * b) :=
  AddMonoidAlgebra.mul_def ..

def C : R →+* MvPolynomial σ R :=
  { singleZeroRingHom with toFun := monomial 0 }

variable (R σ)
