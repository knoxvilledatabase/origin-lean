/-
Extracted from Algebra/FreeNonUnitalNonAssocAlgebra.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Free algebras

Given a semiring `R` and a type `X`, we construct the free non-unital, non-associative algebra on
`X` with coefficients in `R`, together with its universal property. The construction is valuable
because it can be used to build free algebras with more structure, e.g., free Lie algebras.

Note that elsewhere we have a construction of the free unital, associative algebra. This is called
`FreeAlgebra`.

## Main definitions

  * `FreeNonUnitalNonAssocAlgebra`
  * `FreeNonUnitalNonAssocAlgebra.lift`
  * `FreeNonUnitalNonAssocAlgebra.of`

## Implementation details

We construct the free algebra as the magma algebra, with coefficients in `R`, of the free magma on
`X`. However we regard this as an implementation detail and thus deliberately omit the lemmas
`of_apply` and `lift_apply`, and we mark `FreeNonUnitalNonAssocAlgebra` and `lift` as
irreducible once we have established the universal property.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/

open scoped MonoidAlgebra

variable (R X A : Type*) [Semiring R]

abbrev FreeNonUnitalNonAssocAlgebra := R[FreeMagma X]

namespace FreeNonUnitalNonAssocAlgebra

variable {X A}

def of : X → FreeNonUnitalNonAssocAlgebra R X :=
  MonoidAlgebra.ofMagma R _ ∘ FreeMagma.of

variable [NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

def lift : (X → A) ≃ (FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :=
  FreeMagma.lift.trans (MonoidAlgebra.liftMagma R)
