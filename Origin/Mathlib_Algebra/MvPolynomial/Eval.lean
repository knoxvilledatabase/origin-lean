/-
Extracted from Algebra/MvPolynomial/Eval.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Multivariate polynomials

This file defines functions for evaluating multivariate polynomials.
These include generically evaluating a polynomial given a valuation of all its variables,
and more advanced evaluations that allow one to map the coefficients to different rings.

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

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.
* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`
* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`
* `aeval (g : σ → S₁) p` : evaluates the multivariate polynomial obtained from `p` by the change
  of coefficient semiring corresponding to `g` (`a` stands for `Algebra`)

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Eval₂

variable (f : R →+* S₁) (g : σ → S₁)

def eval₂ (p : MvPolynomial σ R) : S₁ :=
  (AddMonoidAlgebra.coeff p).sum fun s a => f a * s.prod fun n e => g n ^ e

theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i, X i ^ d i := by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl
