/-
Extracted from RingTheory/Polynomial/Nilpotent.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nilpotency in polynomial rings.

This file is a place for results related to nilpotency in (single-variable) polynomial rings.

## Main results:
* `Polynomial.isNilpotent_iff`
* `Polynomial.isUnit_iff_coeff_isUnit_isNilpotent`

-/

namespace Polynomial

variable {R : Type*} {r : R}

section Semiring

variable [Semiring R] {P : R[X]}

lemma isNilpotent_C_mul_pow_X_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent ((C r) * X ^ n) := by
  refine Commute.isNilpotent_mul_right (commute_X_pow _ _).symm ?_
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, ?_⟩
  rw [← C_pow, hm, C_0]

lemma isNilpotent_pow_X_mul_C_of_isNilpotent (n : ℕ) (hnil : IsNilpotent r) :
    IsNilpotent (X ^ n * (C r)) := by
  rw [commute_X_pow]
  exact isNilpotent_C_mul_pow_X_of_isNilpotent n hnil
