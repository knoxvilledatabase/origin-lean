/-
Extracted from Algebra/Module/Submodule/Map.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `map` and `comap` for `Submodule`s

## Main declarations

* `Submodule.map`: The pushforward of a submodule `p ⊆ M` by `f : M → M₂`
* `Submodule.comap`: The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`
* `Submodule.giMapComap`: `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
* `Submodule.gciMapComap`: `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.

## Tags

submodule, subspace, linear map, pushforward, pullback
-/

open Function Pointwise Set

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)

variable {x : M}

variable [RingHomSurjective σ₁₂]

def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }
