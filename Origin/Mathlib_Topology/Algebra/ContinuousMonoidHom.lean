/-
Extracted from Topology/Algebra/ContinuousMonoidHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/

assert_not_exists ContinuousLinearMap

assert_not_exists ContinuousLinearEquiv

open Function Topology

variable (F A B C D E : Type*)

variable [Monoid A] [Monoid B] [Monoid C] [Monoid D]

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B, C(A, B)
