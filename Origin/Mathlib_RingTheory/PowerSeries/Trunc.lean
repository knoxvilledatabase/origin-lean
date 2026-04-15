/-
Extracted from RingTheory/PowerSeries/Trunc.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Formal power series in one variable - Truncation

`PowerSeries.trunc n φ` truncates a (univariate) formal power series
to the polynomial that has the same coefficients as `φ`, for all `m < n`,
and `0` otherwise.

-/

noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section Trunc

variable [Semiring R]

open Finset Nat

set_option backward.privateInPublic true in

private def trunc_aux (n : ℕ) (φ : R⟦X⟧) : R[X] :=
  ∑ m ∈ Ico 0 n, Polynomial.monomial m (coeff m φ)

private theorem coeff_trunc_aux (m) (n) (φ : R⟦X⟧) :
    (trunc_aux n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [trunc_aux, Polynomial.coeff_monomial]

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def trunc (n : ℕ) : R⟦X⟧ →ₗ[R] R[X] where
  toFun := trunc_aux n
  map_add' φ ψ := Polynomial.ext fun m => by
    simp only [coeff_trunc_aux, Polynomial.coeff_add]
    split_ifs with H
    · rfl
    · rw [zero_add]
  map_smul' t φ := by ext; simp [trunc_aux, Polynomial.coeff_monomial]

theorem coeff_trunc (m) (n) (φ : R⟦X⟧) :
    (trunc n φ).coeff m = if m < n then coeff m φ else 0 := by
  simp [trunc, coeff_trunc_aux]
