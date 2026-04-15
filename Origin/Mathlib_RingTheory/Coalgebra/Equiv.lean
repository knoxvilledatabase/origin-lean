/-
Extracted from RingTheory/Coalgebra/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms of `R`-coalgebras

This file defines bundled isomorphisms of `R`-coalgebras. We largely mirror the basic API of
`Mathlib/Algebra/Module/Equiv/Defs.lean`.

## Main definitions

* `CoalgEquiv R A B`: the type of `R`-coalgebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₗc[R] B` : `R`-coalgebra equivalence from `A` to `B`.
-/

universe u v w

variable {R A B C : Type*}

open Coalgebra

structure CoalgEquiv (R : Type*) [CommSemiring R] (A B : Type*)
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
    [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →ₗc[R] B, A ≃ₗ[R] B where

attribute [nolint docBlame] CoalgEquiv.toCoalgHom

attribute [nolint docBlame] CoalgEquiv.toLinearEquiv
