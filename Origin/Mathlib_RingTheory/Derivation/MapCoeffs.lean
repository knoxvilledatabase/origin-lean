/-
Extracted from RingTheory/Derivation/MapCoeffs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Coefficient-wise derivation on polynomials

In this file we define applying a derivation on the coefficients of a polynomial,
show this forms a derivation, and prove `apply_eval_eq`, which shows that for a derivation `D`,
`D(p(x)) = (D.mapCoeffs p)(x) + D(x) * p'(x)`. `apply_aeval_eq` and `apply_aeval_eq'`
are generalizations of that for algebras. We also have a special case for `DifferentialAlgebra`s.
-/

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M)

set_option backward.isDefEq.respectTransparency false in

def mapCoeffs : Derivation R A[X] (PolynomialModule A M) where
  __ := (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := show (Finsupp.single 0 1).mapRange (d : A → M) d.map_zero = 0 by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b =>
        refine Finsupp.ext fun i ↦ ?_
        dsimp [PolynomialModule.equivPolynomial, PolynomialModule.map]
        simp only [toFinsupp_mul, toFinsupp_monomial, AddMonoidAlgebra.single_mul_single]
        change d _ = _ + _
        -- TODO: copy more `Finsupp` API to `PolynomialModule`.
        -- We have to do a bit of work to go through the identification
        -- `PolynomialModule A M = ℕ →₀ M`...
        dsimp only [PolynomialModule, Finsupp.mapRange.linearMap_apply, coeFn_coe]
        rw [Finsupp.mapRange_single, Finsupp.mapRange_single]
        -- ... and here we go back through the identification.
        change _ = (_ • PolynomialModule.single A _ _) _ + (_ • PolynomialModule.single A _ _) i
        simp only [PolynomialModule.monomial_smul_single, AddMonoidAlgebra.single_apply,
          apply_ite d, leibniz, map_zero, PolynomialModule.single_apply, ite_add_zero,
          add_comm m n]
