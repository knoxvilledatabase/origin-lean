/-
Extracted from RingTheory/Ideal/Over.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

assert_not_exists Algebra.IsIntegral

assert_not_exists Module.Finite

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule

open scoped Pointwise

section CommRing

variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

variable {p : Ideal R} {P : Ideal S}

theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))) :
    comap (algebraMap R S) P = p := by
  ext x
  rw [mem_comap, ← Quotient.eq_zero_iff_mem, ← Quotient.eq_zero_iff_mem, Quotient.mk_algebraMap,
    IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P), Quotient.algebraMap_eq]
  exact map_eq_zero_iff _ h

variable [Algebra R S]

-- INSTANCE (free from Core): Quotient.algebraQuotientMapQuotient
