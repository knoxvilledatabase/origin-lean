/-
Extracted from Algebra/EuclideanDomain/Basic.lean
Genuine: 1 of 3 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# Lemmas about Euclidean domains

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/

universe u

namespace EuclideanDomain

variable {R : Type u}

variable [EuclideanDomain R]

local infixl:50 " ≺ " => EuclideanDomain.r

-- INSTANCE (free from Core): (priority

theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

-- DISSOLVED: val_dvd_le
