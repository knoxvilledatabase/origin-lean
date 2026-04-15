/-
Extracted from Topology/Algebra/Algebra/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms of topological algebras

This file contains an API for `ContinuousAlgEquiv R A B`, the type of
continuous `R`-algebra isomorphisms with continuous inverses. Here `R` is a
commutative (semi)ring, and `A` and `B` are `R`-algebras with topologies.

## Main definitions

Let `R` be a commutative semiring and let `A` and `B` be `R`-algebras which
are also topological spaces.

* `ContinuousAlgEquiv R A B`: the type of continuous `R`-algebra isomorphisms
  from `A` to `B` with continuous inverses.

## Notation

`A ≃A[R] B` : notation for `ContinuousAlgEquiv R A B`.

## Tags

* continuous, isomorphism, algebra
-/

open scoped Topology

structure ContinuousAlgEquiv (R A B : Type*) [CommSemiring R]
    [Semiring A] [TopologicalSpace A] [Semiring B] [TopologicalSpace B] [Algebra R A]
    [Algebra R B] extends A ≃ₐ[R] B, A ≃ₜ B
