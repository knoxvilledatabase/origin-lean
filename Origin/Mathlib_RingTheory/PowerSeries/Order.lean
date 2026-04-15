/-
Extracted from RingTheory/PowerSeries/Order.lean
Genuine: 1 of 2 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.min_order_le_order_add`).

We prove that if the commutative ring `R` of coefficients is an integral domain,
then the ring `R⟦X⟧` of formal power series in one variable over `R`
is an integral domain.

Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order. This is useful when
proving that `R⟦X⟧` is a normalization monoid, which is done in `PowerSeries.Inverse`.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section OrderBasic

variable [Semiring R] {φ : R⟦X⟧}

-- DISSOLVED: exists_coeff_ne_zero_iff_ne_zero

def order (φ : R⟦X⟧) : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)
