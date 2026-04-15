/-
Extracted from LinearAlgebra/TensorProduct/DirectLimit.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor product and direct limits commute with each other.

Given a family of `R`-modules `Gᵢ` with a family of compatible `R`-linear maps `fᵢⱼ : Gᵢ → Gⱼ` for
every `i ≤ j` and another `R`-module `M`, we have `(limᵢ Gᵢ) ⊗ M` and `lim (Gᵢ ⊗ M)` are isomorphic
as `R`-modules.

## Main definitions:

* `TensorProduct.directLimitLeft : DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M)`
* `TensorProduct.directLimitRight : M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f)`

-/

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommSemiring R]

variable {ι : Type*}

variable [DecidableEq ι] [Preorder ι]

variable {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]

variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable (M : Type*) [AddCommMonoid M] [Module R M]

local notation M " ◁ " f => fun i j h ↦ LinearMap.lTensor M (f _ _ h)

local notation f " ▷ " N => fun i j h ↦ LinearMap.rTensor N (f _ _ h)

namespace TensorProduct

noncomputable def fromDirectLimit :
    DirectLimit (G · ⊗[R] M) (f ▷ M) →ₗ[R] DirectLimit G f ⊗[R] M :=
  Module.DirectLimit.lift _ _ _ _ (fun _ ↦ (of _ _ _ _ _).rTensor M)
    fun _ _ _ x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop

variable {M} in
