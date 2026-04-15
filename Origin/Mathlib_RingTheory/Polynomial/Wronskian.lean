/-
Extracted from RingTheory/Polynomial/Wronskian.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Wronskian of a pair of polynomial

This file defines Wronskian of a pair of polynomials, which is `W(a, b) = ab' - a'b`.
We also prove basic properties of it.

## Main declarations

- `Polynomial.wronskian_eq_of_sum_zero`: We have `W(a, b) = W(b, c)` when `a + b + c = 0`.
- `Polynomial.degree_wronskian_lt_add`: Degree of Wronskian `W(a, b)` is strictly smaller than
  the sum of degrees of `a` and `b`
- `Polynomial.natDegree_wronskian_lt_add`: `natDegree` version of the above theorem.
  We need to assume that the Wronskian is nonzero. (Otherwise, `a = b = 1` gives a counterexample.)

## TODO

- Define Wronskian for n-tuple of polynomials, not necessarily two.
-/

noncomputable section

open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

variable (R) in

def wronskianBilin : R[X] →ₗ[R] R[X] →ₗ[R] R[X] :=
  (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative
