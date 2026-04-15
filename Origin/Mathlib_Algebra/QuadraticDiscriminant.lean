/-
Extracted from Algebra/QuadraticDiscriminant.lean
Genuine: 4 of 12 | Dissolved: 7 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend

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

open Filter

section Ring

variable {R : Type*}

def discrim [Ring R] (a b c : R) : R :=
  b ^ 2 - 4 * a * c

@[simp] lemma discrim_neg [Ring R] (a b c : R) : discrim (-a) (-b) (-c) = discrim a b c := by
  simp [discrim]

variable [CommRing R] {a b c : R}

lemma discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * (x * x) + b * x + c = 0) :
    discrim a b c = (2 * a * x + b) ^ 2 := by
  rw [discrim]
  linear_combination -4 * a * h

-- DISSOLVED: quadratic_eq_zero_iff_discrim_eq_sq

-- DISSOLVED: quadratic_ne_zero_of_discrim_ne_sq

end Ring

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

-- DISSOLVED: quadratic_eq_zero_iff

-- DISSOLVED: exists_quadratic_eq_zero

-- DISSOLVED: quadratic_eq_zero_iff_of_discrim_eq_zero

end Field

section LinearOrderedField

variable {K : Type*} [LinearOrderedField K] {a b c : K}

theorem discrim_le_zero (h : ∀ x : K, 0 ≤ a * (x * x) + b * x + c) : discrim a b c ≤ 0 := by
  rw [discrim, sq]
  obtain ha | rfl | ha : a < 0 ∨ a = 0 ∨ 0 < a := lt_trichotomy a 0
  -- if a < 0
  · have : Tendsto (fun x => (a * x + b) * x + c) atTop atBot :=
      tendsto_atBot_add_const_right _ c
        ((tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop
          tendsto_id)
    rcases (this.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
    exact False.elim ((h x).not_lt <| by rwa [← mul_assoc, ← add_mul])
  -- if a = 0
  · rcases eq_or_ne b 0 with (rfl | hb)
    · simp
    · have := h ((-c - 1) / b)
      rw [mul_div_cancel₀ _ hb] at this
      linarith
  -- if a > 0
  · have ha' : 0 ≤ 4 * a := mul_nonneg zero_le_four ha.le
    convert neg_nonpos.2 (mul_nonneg ha' (h (-b / (2 * a)))) using 1
    field_simp
    ring

lemma discrim_le_zero_of_nonpos (h : ∀ x : K, a * (x * x) + b * x + c ≤ 0) : discrim a b c ≤ 0 :=
  discrim_neg a b c ▸ discrim_le_zero <| by simpa only [neg_mul, ← neg_add, neg_nonneg]

-- DISSOLVED: discrim_lt_zero

-- DISSOLVED: discrim_lt_zero_of_neg

end LinearOrderedField
