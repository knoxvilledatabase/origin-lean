/-
Extracted from RingTheory/Polynomial/Opposites.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Interactions between `R[X]` and `Rᵐᵒᵖ[X]`

This file contains the basic API for "pushing through" the isomorphism
`opRingEquiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X]`.  It allows going back and forth between a polynomial ring
over a semiring and the polynomial ring over the opposite semiring. -/

open Polynomial

open MulOpposite

variable {R : Type*} [Semiring R]

noncomputable section

namespace Polynomial

def opRingEquiv (R : Type*) [Semiring R] : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
  ((toFinsuppIso R).op.trans <| AddMonoidAlgebra.opRingEquiv.trans <|
    AddMonoidAlgebra.mapDomainRingEquiv _ AddOpposite.opAddEquiv.symm).trans (toFinsuppIso _).symm

/-!  Lemmas to get started, using `opRingEquiv R` on the various expressions of
`Finsupp.single`: `monomial`, `C a`, `X`, `C a * X ^ n`. -/

set_option backward.isDefEq.respectTransparency false in
