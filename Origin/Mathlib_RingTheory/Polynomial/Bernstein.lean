/-
Extracted from RingTheory/Polynomial/Bernstein.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernsteinPolynomial (R : Type*) [CommRing R] (n ν : ℕ) : R[X] :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : Fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(Finset.range (n + 1)).sum (fun ν ↦ bernsteinPolynomial R n ν) = 1`
* `(Finset.range (n + 1)).sum (fun ν ↦ ν • bernsteinPolynomial R n ν) = n • X`
* `(Finset.range (n + 1)).sum (fun ν ↦ (ν * (ν-1)) • bernsteinPolynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `Mathlib/Analysis/SpecialFunctions/Bernstein.lean`, which defines the Bernstein
approximations of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly
to `f`.
-/

noncomputable section

open Nat (choose)

open Polynomial (X)

open scoped Polynomial

variable (R : Type*) [CommRing R]

def bernsteinPolynomial (n ν : ℕ) : R[X] :=
  (choose n ν : R[X]) * X ^ ν * (1 - X) ^ (n - ν)

example : bernsteinPolynomial ℤ 3 2 = 3 * X ^ 2 - 3 * X ^ 3 := by

  norm_num [bernsteinPolynomial, choose]

  ring

namespace bernsteinPolynomial

theorem eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernsteinPolynomial R n ν = 0 := by
  simp [bernsteinPolynomial, Nat.choose_eq_zero_of_lt h]

variable {R} {S : Type*} [CommRing S]
