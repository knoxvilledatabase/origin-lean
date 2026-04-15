/-
Extracted from Algebra/Algebra/NonUnitalHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
* an addition,
* an additive zero,
* a multiplication,
* a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `Mul` instead of `Group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `NonUnitalAlgHom`.

TODO: add `NonUnitalAlgEquiv` when needed.

## Main definitions

  * `NonUnitalAlgHom`
  * `AlgHom.toNonUnitalAlgHom`

## Tags

non-unital, algebra, morphism
-/

universe u u₁ v w w₁ w₂ w₃

variable {R : Type u} {S : Type u₁}

structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B
