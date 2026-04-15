/-
Extracted from RingTheory/MvPolynomial/Homogeneous.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homogeneous polynomials

A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occurring in `φ` have degree `n`.

## Main definitions/lemmas

* `IsHomogeneous φ n`: a predicate that asserts that `φ` is homogeneous of degree `n`.
* `homogeneousSubmodule σ R n`: the submodule of homogeneous polynomials of degree `n`.
* `homogeneousComponent n`: the additive morphism that projects polynomials onto
  their summand that is homogeneous of degree `n`.
* `sum_homogeneousComponent`: every polynomial is the sum of its homogeneous components.

## Library notes

* The `MvPolynomial.weightedGradedAlgebra` instance provides a `GradedAlgebra` structure, yielding
  the isomorphism `MvPolynomial σ R ≃ₐ[R] ⨁ m, weightedHomogeneousSubmodule R w m` for a weight
  function `w`.
* The special case with `w = 1` of the above yields the algebra isomorphism
  `MvPolynomial σ R ≃ₐ[R] ⨁ i, homogeneousSubmodule σ R i`.
-/

namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

open Finsupp

def IsHomogeneous [CommSemiring R] (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n

variable [CommSemiring R]
