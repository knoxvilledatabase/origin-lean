/-
Extracted from RingTheory/IntegralClosure/IsIntegral/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R.

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `RingHom.IsIntegralElem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `IsIntegral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                          coefficients in `R`.
-/

open Polynomial

section Ring

variable {R S A : Type*}

variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0
