/-
Extracted from Algebra/Module/LinearMap/Polynomial.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
  `Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map_eq_charpoly`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.
* `LinearMap.nilRank`: the smallest index at which `polyCharpoly` has a non-zero coefficient,
  which is independent of the choice of basis for `L`.
* `LinearMap.IsNilRegular`: an element `x` of `L` is *nil-regular* with respect to `φ`
  if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero,
  where `n` denotes the nil-rank of `φ`.

## Implementation details

We show that `LinearMap.polyCharpoly` does not depend on the choice of basis of the target module.
This is done via `LinearMap.polyCharpoly_eq_polyCharpolyAux`
and `LinearMap.polyCharpolyAux_basisIndep`.
The latter is proven by considering
the base change of the `R`-linear map `φ : L →ₗ[R] End R M`
to the multivariate polynomial ring `MvPolynomial ι R`,
and showing that `polyCharpolyAux φ` is equal to the characteristic polynomial of this base change.
The proof concludes because characteristic polynomials are independent of the chosen basis.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

open Module MvPolynomial

open scoped Matrix

namespace Matrix

variable {m n o R S : Type*}

variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

noncomputable

def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)

lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n → R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

lemma toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp [Finsupp.degree, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same]

lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le
