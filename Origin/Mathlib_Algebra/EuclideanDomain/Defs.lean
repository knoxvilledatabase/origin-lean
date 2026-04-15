/-
Extracted from Algebra/EuclideanDomain/Defs.lean
Genuine: 17 of 28 | Dissolved: 7 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.RelClasses

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `EuclideanDomain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `Div` and `Mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `Algebra.EuclideanDomain.Basic` for most of the theorems about Euclidean domains,
including Bézout's lemma.

See `Algebra.EuclideanDomain.Instances` for the fact that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `EuclideanDomain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/

universe u

-- DISSOLVED: EuclideanDomain

namespace EuclideanDomain

variable {R : Type u} [EuclideanDomain R]

local infixl:50 " ≺ " => EuclideanDomain.r

local instance wellFoundedRelation : WellFoundedRelation R where
  wf := r_wellFounded

instance isWellFounded : IsWellFounded R (· ≺ ·) where
  wf := r_wellFounded

instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _

theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

-- DISSOLVED: mod_lt

-- DISSOLVED: mul_right_not_lt

@[simp]
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0

theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 :=
  haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h

-- DISSOLVED: val_dvd_le

-- DISSOLVED: div_zero

section

-- DISSOLVED: GCD.induction

termination_by a

end

section GCD

variable [DecidableEq R]

def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a

termination_by a

@[simp]
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl

def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t

termination_by r

@[simp]
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcdAux
  exact if_pos rfl

-- DISSOLVED: xgcdAux_rec

def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2

def gcdA (x y : R) : R :=
  (xgcd x y).1

def gcdB (x y : R) : R :=
  (xgcd x y).2

@[simp]
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]

theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  rfl

end GCD

section LCM

variable [DecidableEq R]

def lcm (x y : R) : R :=
  x * y / gcd x y

end LCM

end EuclideanDomain
