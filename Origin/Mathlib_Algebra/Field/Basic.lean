/-
Extracted from Algebra/Field/Basic.lean
Genuine: 1 of 13 | Dissolved: 12 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

open Function OrderDual Set

universe u

variable {K L : Type*}

section DivisionSemiring

variable [DivisionSemiring K] {a b c d : K}

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

-- DISSOLVED: same_add_div

-- DISSOLVED: div_add_same

-- DISSOLVED: one_add_div

-- DISSOLVED: div_add_one

-- DISSOLVED: inv_add_inv'

-- DISSOLVED: one_div_mul_add_mul_one_div_eq_one_div_add_one_div

-- DISSOLVED: add_div_eq_mul_add_div

-- DISSOLVED: add_div'

-- DISSOLVED: div_add'

-- DISSOLVED: Commute.div_add_div

-- DISSOLVED: Commute.one_div_add_one_div

-- DISSOLVED: Commute.inv_add_inv

variable [NeZero (2 : K)]
