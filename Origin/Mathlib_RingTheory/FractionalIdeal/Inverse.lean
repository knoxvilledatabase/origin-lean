/-
Extracted from RingTheory/FractionalIdeal/Inverse.lean
Genuine: 5 of 12 | Dissolved: 5 | Infrastructure: 2
-/
import Origin.Core

/-!
# Inverse operator for fractional ideals

This file defines the notation `I⁻¹` where `I` is a not necessarily invertible fractional ideal.
Note that this is somewhat misleading notation in case `I` is not invertible.
The theorem that all nonzero fractional ideals are invertible in a Dedekind domain can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `FractionalIdeal.instInv` defines `I⁻¹ := 1 / I`.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

fractional ideal, invertible ideal
-/

assert_not_exists IsDedekindDomain

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]

variable {I J : FractionalIdeal R₁⁰ K}

-- INSTANCE (free from Core): :

-- DISSOLVED: inv_zero'

-- DISSOLVED: inv_of_ne_zero

-- DISSOLVED: coe_inv_of_ne_zero

variable {K}

-- DISSOLVED: mem_inv_iff

-- DISSOLVED: inv_anti_mono

theorem le_self_mul_inv {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * I⁻¹ :=
  le_self_mul_one_div hI

variable (K)

theorem coe_ideal_le_self_mul_inv (I : Ideal R₁) :
    (I : FractionalIdeal R₁⁰ K) ≤ I * (I : FractionalIdeal R₁⁰ K)⁻¹ :=
  le_self_mul_inv coeIdeal_le_one

theorem right_inverse_eq (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : J = I⁻¹ :=
  eq_one_div_of_mul_eq_one_right _ _ h

theorem mul_inv_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨I⁻¹, h⟩, fun ⟨J, hJ⟩ => by rwa [← right_inverse_eq K I J hJ]⟩

theorem mul_inv_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} : I * I⁻¹ = 1 ↔ IsUnit I :=
  (mul_inv_cancel_iff K).trans isUnit_iff_exists_inv.symm

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']
