/-
Extracted from Analysis/SpecialFunctions/Trigonometric/Arctan.lean
Genuine: 6 of 7 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# The `arctan` function.

Inequalities, identities and `Real.tan` as an `OpenPartialHomeomorph` between `(-(π / 2), π / 2)`
and the whole line.

The result of `arctan x + arctan y` is given by `arctan_add`, `arctan_add_eq_add_pi` or
`arctan_add_eq_sub_pi` depending on whether `x * y < 1` and `0 < x`. As an application of
`arctan_add` we give four Machin-like formulas (linear combinations of arctangents equal to
`π / 4 = arctan 1`), including John Machin's original one at
`four_mul_arctan_inv_5_sub_arctan_inv_239`.
-/

noncomputable section

open Set Filter

open scoped Topology

namespace Real

variable {x y : ℝ}

theorem tan_add
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using
    @Complex.tan_add (x : ℂ) (y : ℂ) (by convert h <;> norm_cast)

theorem tan_add'
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) :=
  tan_add (Or.inl h)

theorem tan_sub {x y : ℝ}
    (h : ((∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) ∨
      (∃ k : ℤ, x = (2 * k + 1) * π / 2) ∧ ∃ l : ℤ, y = (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  simpa only [← Complex.ofReal_inj, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_tan] using
    @Complex.tan_sub (x : ℂ) (y : ℂ) (by convert h <;> norm_cast)

theorem tan_sub' {x y : ℝ}
    (h : (∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) ∧ ∀ l : ℤ, y ≠ (2 * l + 1) * π / 2) :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) :=
  tan_sub (Or.inl h)

theorem tan_two_mul : tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) := by
  have := @Complex.tan_two_mul x
  norm_cast at *

theorem tan_int_mul_pi_div_two (n : ℤ) : tan (n * π / 2) = 0 :=
  tan_eq_zero_iff.mpr (by use n)

-- DISSOLVED: continuousOn_tan
