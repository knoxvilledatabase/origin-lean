/-
Extracted from Algebra/MvPolynomial/Expand.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
## Expand multivariate polynomials

Given a multivariate polynomial `φ`, one may replace every occurrence of `X i` by `X i ^ n`,
for some natural number `n`.
This operation is called `MvPolynomial.expand` and it is an algebra homomorphism.

### Main declaration

* `MvPolynomial.expand`: expand a polynomial by a factor of p, so `∑ aₙ xⁿ` becomes `∑ aₙ xⁿᵖ`.
-/

namespace MvPolynomial

section CommSemiring

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

noncomputable def expand : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  bind₁ fun i ↦ X i ^ p

theorem expand_C (r : R) : expand p (C r : MvPolynomial σ R) = C r :=
  eval₂Hom_C _ _ _
