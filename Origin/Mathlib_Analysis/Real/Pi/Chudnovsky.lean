/-
Extracted from Analysis/Real/Pi/Chudnovsky.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

meta import Batteries.Data.Rat.Float  -- shake: keep (for `#eval` sanity check)

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing `π⁻¹`.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem,
but at present we are a long way off.

## Main definitions

* `chudnovskySum`: The infinite sum in Chudnovsky's formula

## Future work

* Use this formula to give approximations for `π`.
* Prove the sum equals `π⁻¹`, as stated using `proof_wanted` below.
* Show that each imaginary quadratic field of class number 1 (corresponding to Heegner numbers)
  gives a Ramanujan type formula, and that this is the formula coming from 163,
  with `j ((1 + √-163) / 2) = -640320^3`, and the other magic constants coming from
  Eisenstein series.

## References
* [Milla, *A detailed proof of the Chudnovsky formula*][Milla_2018]
* [Chen and Glebov, *On Chudnovsky--Ramanujan type formulae*][Chen_Glebov_2018]

-/

open scoped Real

open Nat

def chudnovskyNum (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (6 * n)! * (545140134 * n + 13591409)

def chudnovskyDenom (n : ℕ) : ℕ :=
  (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

def chudnovskyTerm (n : ℕ) : ℚ :=
  chudnovskyNum n / chudnovskyDenom n

#guard_msgs in

#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *

  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

noncomputable def chudnovskySum : ℝ :=
  12 / (640320 : ℝ) ^ (3 / 2 : ℝ) * ∑' n : ℕ, (chudnovskyTerm n : ℝ)

proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹
