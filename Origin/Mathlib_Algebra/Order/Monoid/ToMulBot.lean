/-
Extracted from Algebra/Order/Monoid/ToMulBot.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

noncomputable section

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

variable [Preorder α] (a b : WithZero (Multiplicative α))

theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id

end WithZero
