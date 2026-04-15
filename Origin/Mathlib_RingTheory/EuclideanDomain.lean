/-
Extracted from RingTheory/EuclideanDomain.lean
Genuine: 4 | Conflates: 0 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

section

open EuclideanDomain Set Ideal

section GCDMonoid

variable {R : Type*} [EuclideanDomain R] [GCDMonoid R] {p q : R}

-- DISSOLVED: gcd_ne_zero_of_left

-- DISSOLVED: gcd_ne_zero_of_right

-- DISSOLVED: left_div_gcd_ne_zero

-- DISSOLVED: right_div_gcd_ne_zero

-- DISSOLVED: isCoprime_div_gcd_div_gcd

end GCDMonoid

namespace EuclideanDomain

def gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

variable {α : Type*} [EuclideanDomain α]

theorem span_gcd [DecidableEq α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

theorem gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

-- DISSOLVED: isCoprime_of_dvd

theorem dvd_or_coprime (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_coprime x y h

end EuclideanDomain

end
