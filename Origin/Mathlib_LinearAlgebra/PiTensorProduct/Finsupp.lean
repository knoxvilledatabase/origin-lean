/-
Extracted from LinearAlgebra/PiTensorProduct/Finsupp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results on finitely supported functions.

* `ofFinsuppEquiv`, the tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly
  equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/

namespace PiTensorProduct

open PiTensorProduct TensorProduct

attribute [local ext] TensorProduct.ext

variable {R ι : Type*} {κ M : ι → Type*}

variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, DecidableEq (M i)]

noncomputable def ofFinsuppEquiv :
    (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  haveI := Classical.typeDecidableEq (⨂[R] (i : ι), M i)
  PiTensorProduct.congr (fun _ ↦ finsuppLequivDFinsupp R) ≪≫ₗ
    ofDFinsuppEquiv ≪≫ₗ
    (finsuppLequivDFinsupp R).symm
