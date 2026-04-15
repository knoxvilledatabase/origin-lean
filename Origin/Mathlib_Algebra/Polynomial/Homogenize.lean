/-
Extracted from Algebra/Polynomial/Homogenize.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homogenize a univariate polynomial

In this file we define a function `Polynomial.homogenize p n`
that takes a polynomial `p` and a natural number `n`
and returns a homogeneous bivariate polynomial of degree `n`.

If `n` is at least the degree of `p`, then `(homogenize p n).eval ![x, 1] = p.eval x`.

We use `MvPolynomial (Fin 2) R` to represent bivariate polynomials
instead of `R[X][Y]` (i.e., `Polynomial (Polynomial R)`),
because Mathlib has a theory about homogeneous multivariate polynomials,
but not about homogeneous bivariate polynomials encoded as `R[X][Y]`.
-/

open Finset

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R]

noncomputable def homogenize (p : R[X]) (n : ℕ) : MvPolynomial (Fin 2) R :=
  ∑ kl ∈ antidiagonal n, .monomial (fun₀ | 0 => kl.1 | 1 => kl.2) (p.coeff kl.1)
