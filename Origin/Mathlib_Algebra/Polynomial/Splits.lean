/-
Extracted from Algebra/Polynomial/Splits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Split polynomials

A polynomial `f : R[X]` splits if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Splits f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

def Splits (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})
