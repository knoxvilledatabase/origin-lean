/-
Extracted from Algebra/QuadraticDiscriminant.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * (x * x) + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.
- `discrim_le_zero_of_nonpos`, `discrim_lt_zero`, `discrim_lt_zero_of_neg`: versions of this
  statement with other inequalities.

## Tags

polynomial, quadratic, discriminant, root
-/

assert_not_exists Finite Finset

open Filter

section Ring

variable {R : Type*}

def discrim [Ring R] (a b c : R) : R :=
  b ^ 2 - 4 * a * c
