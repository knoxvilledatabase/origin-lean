/-
Extracted from Algebra/MonoidAlgebra/Lift.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lifting monoid algebras

This file defines `liftNC`. For the definition of `MonoidAlgebra.lift`, see
`Mathlib/Algebra/MonoidAlgebra/Basic.lean`.

## Main results
* `MonoidAlgebra.liftNC`, `AddMonoidAlgebra.liftNC`: lift a homomorphism `f : k →+ R` and a
  function `g : G → R` to a homomorphism `k[G] →+ R`.
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

noncomputable section

open Finsupp hiding single

universe u₁ u₂ u₃ u₄

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S T M : Type*}

/-! ### Multiplicative monoids -/

namespace MonoidAlgebra

variable {k G}

variable [Semiring k] [NonUnitalNonAssocSemiring R]

def liftNC (f : k →+ R) (g : G → R) : k[G] →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g x)).comp f
