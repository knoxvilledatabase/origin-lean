/-
Extracted from RingTheory/IsTensorProduct.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The characteristic predicate of tensor product

## Main definitions

- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `IsBaseChange`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being an
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `Algebra.IsPushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
  asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/

universe u v₁ v₂ v₃ v₄

open TensorProduct

section IsTensorProduct

variable {R : Type*} [CommSemiring R]

variable {M₁ M₂ M M' : Type*}

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']

variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)

variable {N₁ N₂ N : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]

variable [Module R N₁] [Module R N₂] [Module R N]

variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)

variable (R M N) {f}

theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) := by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

namespace IsTensorProduct

variable {R M N}
