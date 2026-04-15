/-
Extracted from Algebra/Star/Conjneg.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conjugation-negation operator

This file defines the conjugation-negation operator, useful in Fourier analysis.

The way this operator enters the picture is that the adjoint of convolution with a function `f` is
convolution with `conjneg f`.
-/

open Function

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

section CommSemiring

variable [CommSemiring R] [StarRing R] {f g : G → R}

def conjneg (f : G → R) : G → R := conj fun x ↦ f (-x)
