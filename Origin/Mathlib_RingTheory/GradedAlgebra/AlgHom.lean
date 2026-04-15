/-
Extracted from RingTheory/GradedAlgebra/AlgHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `R`-linear homomorphisms of graded algebras

This file defines bundled `R`-linear homomorphisms of graded `R`-algebras.

## Main definitions

* `GradedAlgHom R 𝒜 ℬ`: the type of `R`-linear homomorphisms of `R`-graded algebras `𝒜` to `ℬ`.

## Notation

* `𝒜 →ₐᵍ[R] ℬ` : `R`-linear graded homomorphism from `𝒜` to `ℬ`.
-/

structure GradedAlgHom (R : Type*) {A B ι : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [DecidableEq ι] [AddMonoid ι]
    (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    extends A →ₐ[R] B, 𝒜 →+*ᵍ ℬ

add_decl_doc GradedAlgHom.toGradedRingHom
