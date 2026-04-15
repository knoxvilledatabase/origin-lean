/-
Extracted from RingTheory/GradedAlgebra/RingHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of graded (semi)rings

This file defines bundled homomorphisms of graded (semi)rings. We use the same structure
`GradedRingHom 𝒜 ℬ`, a.k.a. `𝒜 →+*ᵍ ℬ`, for both types of homomorphisms.

We do **not** define a separate class of graded ring homomorphisms; instead, we use
`[FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]`.

## Main definitions

* `GradedRingHom`: Graded (semi)ring homomorphisms. Ring homomorphism which preserves the grading.

## Notation

* `→+*ᵍ`: Graded (semi)ring hom.

## Implementation notes

* We don't really need the fact that they are graded rings until the theorem
  `DirectSum.decompose_map` which describes how the decomposition interacts with the map.
-/

variable {ι A B C D σ τ ψ ω : Type*}
  [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [SetLike σ A] [SetLike τ B] [SetLike ψ C] [SetLike ω D]

open Graded

section SetLike

structure GradedRingHom (𝒜 : ι → σ) (ℬ : ι → τ) extends A →+* B where
  protected map_mem {i : ι} {x : A} : x ∈ 𝒜 i → toRingHom x ∈ ℬ i

variable {𝒜 : ι → σ} {ℬ : ι → τ} {𝒞 : ι → ψ} {𝒟 : ι → ω}
