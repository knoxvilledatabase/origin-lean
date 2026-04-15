/-
Extracted from Algebra/Algebra/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notation

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

universe u v w u₁ v₁

structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

add_decl_doc AlgHom.toRingHom
