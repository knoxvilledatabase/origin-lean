/-
Extracted from Algebra/Algebra/Equiv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphisms of `R`-algebras

This file defines bundled isomorphisms of `R`-algebras.

## Main definitions

* `AlgEquiv R A B`: the type of `R`-algebra isomorphisms between `A` and `B`.

## Notation

* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.
-/

universe u v w u₁ v₁ u₂ u₃

structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  /-- An equivalence of algebras commutes with the action of scalars. -/
  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

attribute [nolint docBlame] AlgEquiv.toRingEquiv

attribute [nolint docBlame] AlgEquiv.toEquiv

attribute [nolint docBlame] AlgEquiv.toAddEquiv

attribute [nolint docBlame] AlgEquiv.toMulEquiv
