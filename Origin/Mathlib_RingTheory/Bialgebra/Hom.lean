/-
Extracted from RingTheory/Bialgebra/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of `R`-bialgebras

This file defines bundled homomorphisms of `R`-bialgebras. We simply mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `BialgHom R A B`: the type of `R`-bialgebra morphisms from `A` to `B`.
* `Bialgebra.counitBialgHom R A : A →ₐc[R] R`: the counit of a bialgebra as a bialgebra
  homomorphism.

## Notation

* `A →ₐc[R] B` : `R`-bialgebra homomorphism from `A` to `B`.

-/

open TensorProduct Bialgebra Coalgebra Function

universe u v w

structure BialgHom (R A B : Type*) [CommSemiring R]
    [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A →* B

add_decl_doc BialgHom.toMonoidHom
