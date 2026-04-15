/-
Extracted from Data/ENNReal/Inv.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results about division in extended non-negative reals

This file establishes basic properties related to the inversion and division operations on `ℝ≥0∞`.
For instance, as a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation
with integer exponent.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

assert_not_exists Finset

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

protected theorem div_eq_inv_mul : a / b = b⁻¹ * a := by rw [div_eq_mul_inv, mul_comm]

protected theorem div_right_comm : a / b / c = a / c / b := by
  simp only [div_eq_mul_inv, mul_right_comm]
