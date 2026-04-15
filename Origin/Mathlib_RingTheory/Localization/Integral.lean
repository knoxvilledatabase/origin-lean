/-
Extracted from RingTheory/Localization/Integral.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral and algebraic elements of a fraction field

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]

variable [Algebra R S]

open Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable [IsLocalization M S]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in

private theorem exists_integer_polynomial_multiple_and_support_subset (p : S[X]) :
    ∃ b ∈ M, ∃ (q : R[X]), q.map (algebraMap R S) = b • p ∧ q.support ⊆ p.support := by
  obtain ⟨⟨_, b, hb, rfl⟩, h⟩ := exists_integer_multiple (Submonoid.map C M) p
  rw [Subtype.coe_mk, C_eq_algebraMap, algebraMap_smul] at h
  obtain ⟨q', h₁, h₂⟩ := exists_support_eq_of_mem_lifts h
  exact ⟨b, hb, q', h₁, h₂ ▸ support_smul b p⟩
