/-
Extracted from RingTheory/Spectrum/Prime/RingHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functoriality of the prime spectrum

In this file we define the induced map on prime spectra induced by a ring homomorphism.

## Main definitions

* `PrimeSpectrum.comap`: The induced map on prime spectra by a ring homomorphism. The proof that
  it is continuous is in `Mathlib/RingTheory/Spectrum/Prime/Topology.lean`.

-/

universe u v

variable (R : Type u) (S : Type v)

open PrimeSpectrum

def PrimeSpectrum.comap {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : PrimeSpectrum S) : PrimeSpectrum R :=
  ⟨Ideal.comap f p.asIdeal, inferInstance⟩
