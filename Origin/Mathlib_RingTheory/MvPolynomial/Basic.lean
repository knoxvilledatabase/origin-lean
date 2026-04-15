/-
Extracted from RingTheory/MvPolynomial/Basic.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrictTotalDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrictDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative semiring of characteristic `p` has
  characteristic `p`, and similarly for `CharZero`.
* `basisMonomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/

noncomputable section

open Set LinearMap Module Submodule

universe u v

variable (σ : Type u) (R : Type v) [CommSemiring R] (p m : ℕ)

namespace MvPolynomial

-- INSTANCE (free from Core): {σ

section CharP

-- INSTANCE (free from Core): [CharP

end CharP

section CharZero

-- INSTANCE (free from Core): [CharZero

end CharZero

section ExpChar

variable [ExpChar R p]

-- INSTANCE (free from Core): :

end ExpChar

section Homomorphism

set_option backward.isDefEq.respectTransparency false in

theorem mapRange_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
    (f : R →+* S) : Finsupp.mapRange f f.map_zero p = map f p := by
  rw [p.as_sum, Finsupp.mapRange_finset_sum, map_sum (map f)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_monomial, ← single_eq_monomial, Finsupp.mapRange_single, single_eq_monomial]

end Homomorphism

section Degree

variable {σ}

def restrictSupport (s : Set (σ →₀ ℕ)) : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ s

def basisRestrictSupport (s : Set (σ →₀ ℕ)) : Basis s R (restrictSupport R s) where
  repr := Finsupp.supportedEquivFinsupp s

theorem restrictSupport_mono {s t : Set (σ →₀ ℕ)} (h : s ⊆ t) :
    restrictSupport R s ≤ restrictSupport R t := Finsupp.supported_mono h

lemma restrictSupport_eq_span (s : Set (σ →₀ ℕ)) :
    restrictSupport R s = .span _ ((monomial · 1) '' s) := Finsupp.supported_eq_span_single ..

lemma mem_restrictSupport_iff {s : Set (σ →₀ ℕ)} {r : MvPolynomial σ R} :
    r ∈ restrictSupport R s ↔ ↑r.support ⊆ s := .rfl
