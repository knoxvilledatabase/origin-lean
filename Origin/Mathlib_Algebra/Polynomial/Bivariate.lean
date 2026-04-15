/-
Extracted from Algebra/Polynomial/Bivariate.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bivariate polynomials

This file introduces the notation `R[X][Y]` for the polynomial ring `R[X][X]` in two variables,
and the notation `Y` for the second variable, in the `Polynomial.Bivariate` scope.

It also defines `Polynomial.evalEval` for the evaluation of a bivariate polynomial at a point
on the affine plane, which is a ring homomorphism (`Polynomial.evalEvalRingHom`), as well as
the abbreviation `CC` to view a constant in the base ring `R` as a bivariate polynomial.
-/

scoped[Polynomial.Bivariate] notation3:max "Y" => Polynomial.X (R := Polynomial _)

scoped[Polynomial.Bivariate] notation3:max R "[X][Y]" => Polynomial (Polynomial R)

open scoped Polynomial.Bivariate

namespace Polynomial

noncomputable section

variable {R S : Type*}

section Semiring

variable [Semiring R]

abbrev evalEval (x y : R) (p : R[X][Y]) : R := eval x (eval (C y) p)

abbrev CC (r : R) : R[X][Y] := C (C r)

lemma evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval, eval_C]

lemma evalEval_map_C (x y : R) (p : R[X]) : (p.map C).evalEval x y = p.eval y := by
  rw [evalEval, eval_map_apply, eval_C]
