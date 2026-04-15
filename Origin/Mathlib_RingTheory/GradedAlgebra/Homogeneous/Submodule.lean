/-
Extracted from RingTheory/GradedAlgebra/Homogeneous/Submodule.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule 𝒜 ℳ`: The structure extending submodules which satisfy
  `Submodule.IsHomogeneous`.

## Implementation notes

The **notion** of homogeneous submodule does not rely on a graded ring, only a decomposition of the
module. However, most interesting properties of homogeneous submodules do rely on the base ring
being a graded ring. For technical reasons, we make `HomogeneousSubmodule` depend on a graded ring.
For example, if the definition of a homogeneous submodule does not depend on a graded ring, the
instance that `HomogeneousSubmodule` is a complete lattice cannot be synthesized due to
synthesization order.

## Tags

graded algebra, homogeneous
-/

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  SetLike.IsHomogeneous ℳ p

theorem Submodule.IsHomogeneous.mem_iff {p : Submodule A M}
    (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p :=
  AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

structure HomogeneousSubmodule (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
    extends Submodule A M where
  is_homogeneous' : toSubmodule.IsHomogeneous ℳ

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)

variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]

variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]

variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {𝒜 ℳ} in

theorem HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.IsHomogeneous ℳ :=
  p.is_homogeneous'

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ fun (h : x = y) ↦ by simp [h]

-- INSTANCE (free from Core): HomogeneousSubmodule.setLike

-- INSTANCE (free from Core): :
