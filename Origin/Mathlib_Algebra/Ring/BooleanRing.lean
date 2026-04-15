/-
Extracted from Algebra/Ring/BooleanRing.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `BooleanRing`: a typeclass for rings where multiplication is idempotent.
* `BooleanRing.toBooleanAlgebra`: Turn a Boolean ring into a Boolean algebra.
* `BooleanAlgebra.toBooleanRing`: Turn a Boolean algebra into a Boolean ring.
* `AsBoolAlg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `AsBoolRing`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `BooleanAlgebraOfBooleanRing` and
  `BooleanRingOfBooleanAlgebra`.
* Type-synonyms `AsBoolAlg` and `AsBoolRing`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`ofBoolAlg`/`toBoolAlg`/`ofBoolRing`/`toBoolRing` explicitly.

## Tags

boolean ring, boolean algebra
-/

open scoped symmDiff

variable {α β γ : Type*}

class BooleanRing (α) extends Ring α where
  /-- Multiplication in a Boolean ring is idempotent. -/
  isIdempotentElem (a : α) : IsIdempotentElem a

namespace BooleanRing

variable [BooleanRing α] (a b : α)
