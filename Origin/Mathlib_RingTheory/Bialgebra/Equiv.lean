/-
Extracted from RingTheory/Bialgebra/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms of `R`-bialgebras

This file defines bundled isomorphisms of `R`-bialgebras. We simply mimic the early parts of
`Mathlib/Algebra/Algebra/Equiv.lean`.

## Main definitions

* `BialgEquiv R A B`: the type of `R`-bialgebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐc[R] B` : `R`-bialgebra equivalence from `A` to `B`.
-/

universe u v w u₁

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁}

open TensorProduct Coalgebra Bialgebra Function

structure BialgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A ≃ₗc[R] B, A ≃* B where

attribute [nolint docBlame] BialgEquiv.toMulEquiv

attribute [nolint docBlame] BialgEquiv.toCoalgEquiv
