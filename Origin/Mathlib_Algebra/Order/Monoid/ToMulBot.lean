/-
Extracted from Algebra/Order/Monoid/ToMulBot.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _
