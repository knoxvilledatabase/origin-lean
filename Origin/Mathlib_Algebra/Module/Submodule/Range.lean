/-
Extracted from Algebra/Module/Submodule/Range.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Range of linear maps

The range `LinearMap.range` of a (semi)linear map `f : M → M₂` is a submodule of `M₂`.

More specifically, `LinearMap.range` applies to any `SemilinearMapClass` over a `RingHomSurjective`
ring homomorphism.

Note that this also means that dot notation (i.e. `f.range` for a linear map `f`) does not work.

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module, range
-/

open Function

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]

variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}

variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm
