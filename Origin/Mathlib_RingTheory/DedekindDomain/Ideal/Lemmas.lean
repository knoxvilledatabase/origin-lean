/-
Extracted from RingTheory/DedekindDomain/Ideal/Lemmas.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Dedekind domains and ideals

In this file, we prove some results on the unique factorization monoid structure of the ideals.
The unique factorization of ideals and invertibility of fractional ideals can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `IsDedekindDomain.HeightOneSpectrum` defines the type of nonzero prime ideals of `R`.

## Implementation notes

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open Module

open scoped nonZeroDivisors Polynomial

section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

namespace FractionalIdeal

open Ideal

theorem exists_notMem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI1 : I ≠ ⊤) : ∃ x ∈ (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
  Set.not_subset.1 <| not_inv_le_one_of_ne_bot hI0 hI1

end FractionalIdeal

end Inverse

section IsDedekindDomain

variable {R A}

variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

open Ideal
