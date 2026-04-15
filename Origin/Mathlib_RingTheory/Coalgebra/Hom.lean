/-
Extracted from RingTheory/Coalgebra/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of `R`-coalgebras

This file defines bundled homomorphisms of `R`-coalgebras. We largely mimic
`Mathlib/Algebra/Algebra/Hom.lean`.

## Main definitions

* `CoalgHom R A B`: the type of `R`-coalgebra morphisms from `A` to `B`.
* `Coalgebra.counitCoalgHom R A : A →ₗc[R] R`: the counit of a coalgebra as a coalgebra
  homomorphism.

## Notation

* `A →ₗc[R] B` : `R`-coalgebra homomorphism from `A` to `B`.

-/

open TensorProduct Coalgebra

universe u v w

structure CoalgHom (R A B : Type*) [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid B] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗ[R] B where
  counit_comp : counit ∘ₗ toLinearMap = counit
  map_comp_comul : TensorProduct.map toLinearMap toLinearMap ∘ₗ comul = comul ∘ₗ toLinearMap
