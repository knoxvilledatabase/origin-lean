/-
Extracted from FieldTheory/RatFunc/Degree.lean
Genuine: 7 | Conflates: 0 | Dissolved: 4 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Content

/-!
# The degree of rational functions

## Main definitions
We define the degree of a rational function, with values in `ℤ`:
 - `intDegree` is the degree of a rational function, defined as the difference between the
   `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
   `intDegree 0 = 0`.
-/

noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section IntDegree

open Polynomial

variable [Field K]

def intDegree (x : RatFunc K) : ℤ :=
  natDegree x.num - natDegree x.denom

@[simp]
theorem intDegree_zero : intDegree (0 : RatFunc K) = 0 := by
  rw [intDegree, num_zero, natDegree_zero, denom_zero, natDegree_one, sub_self]

@[simp]
theorem intDegree_one : intDegree (1 : RatFunc K) = 0 := by
  rw [intDegree, num_one, denom_one, sub_self]

@[simp]
theorem intDegree_C (k : K) : intDegree (C k) = 0 := by
  rw [intDegree, num_C, natDegree_C, denom_C, natDegree_one, sub_self]

@[simp]
theorem intDegree_X : intDegree (X : RatFunc K) = 1 := by
  rw [intDegree, num_X, Polynomial.natDegree_X, denom_X, Polynomial.natDegree_one,
    Int.ofNat_one, Int.ofNat_zero, sub_zero]

@[simp]
theorem intDegree_polynomial {p : K[X]} :
    intDegree (algebraMap K[X] (RatFunc K) p) = natDegree p := by
  rw [intDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_one,
    Int.ofNat_zero, sub_zero]

-- DISSOLVED: intDegree_mul

@[simp]
theorem intDegree_neg (x : RatFunc K) : intDegree (-x) = intDegree x := by
  by_cases hx : x = 0
  · rw [hx, neg_zero]
  · rw [intDegree, intDegree, ← natDegree_neg x.num]
    exact
      natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
        (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)

-- DISSOLVED: intDegree_add

-- DISSOLVED: natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree

-- DISSOLVED: intDegree_add_le

end IntDegree

end RatFunc
