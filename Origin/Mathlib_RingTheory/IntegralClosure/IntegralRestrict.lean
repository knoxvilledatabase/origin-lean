/-
Extracted from RingTheory/IntegralClosure/IntegralRestrict.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Restriction of various maps between fields to integrally closed subrings.

In this file, we assume `A` is an integrally closed domain; `K` is the fraction ring of `A`;
`L` is a finite extension of `K`; `B` is the integral closure of `A` in `L`.
We call this the AKLB setup.

## Main definitions
- `galRestrict`: The restriction `Aut(L/K) → Aut(B/A)` as an `MulEquiv` in an AKLB setup.
- `Algebra.intTrace`: The trace map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the trace map of `Frac(B)/Frac(A)`.
- `Algebra.intNorm`: The norm map of a finite extension of integrally closed domains `B/A` is
  defined to be the restriction of the norm map of `Frac(B)/Frac(A)`.

-/

open Module nonZeroDivisors

variable (A K L L₂ L₃ B B₂ B₃ : Type*)

variable [CommRing A] [CommRing B] [CommRing B₂] [CommRing B₃]

variable [Algebra A B] [Algebra A B₂] [Algebra A B₃]

variable [Field K] [Field L] [Field L₂] [Field L₃]

variable [Algebra A K] [IsFractionRing A K]

variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]

variable [Algebra K L₃] [Algebra A L₃] [IsScalarTower A K L₃]

variable [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

variable [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]

variable [Algebra B₃ L₃] [IsScalarTower A B₃ L₃] [IsIntegralClosure B₃ A L₃]

section galois

section galRestrict'

variable {K L L₂ L₃}

omit [IsFractionRing A K]

noncomputable

def galRestrict' (f : L →ₐ[K] L₂) : (B →ₐ[A] B₂) :=
  (IsIntegralClosure.equiv A (integralClosure A L₂) L₂ B₂).toAlgHom.comp
      (((f.restrictScalars A).comp (IsScalarTower.toAlgHom A B L)).codRestrict
        (integralClosure A L₂) (fun x ↦ IsIntegral.map _ (IsIntegralClosure.isIntegral A L x)))
