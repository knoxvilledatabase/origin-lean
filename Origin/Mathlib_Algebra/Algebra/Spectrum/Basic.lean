/-
Extracted from Algebra/Algebra/Spectrum/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ (↑ₐ r - a)⁻¹ʳ`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐ r - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_comm` and `spectrum.preimage_units_mul_comm`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

open Set

open scoped Pointwise Ring

universe u v

section Defs

variable (R : Type u) {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}

def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ

variable {R}

noncomputable def resolvent (a : A) (r : R) : A := (↑ₐ r - a)⁻¹ʳ
