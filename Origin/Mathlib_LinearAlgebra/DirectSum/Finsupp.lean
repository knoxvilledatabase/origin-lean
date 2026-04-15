/-
Extracted from LinearAlgebra/DirectSum/Finsupp.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Results on finitely supported functions.

* `TensorProduct.finsuppLeft`, the tensor product of `ι →₀ M` and `N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarLeft`, the tensor product of `ι →₀ R` and `N`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppRight`, the tensor product of `M` and `ι →₀ N`
  is linearly equivalent to `ι →₀ M ⊗[R] N`

* `TensorProduct.finsuppScalarRight`, the tensor product of `M` and `ι →₀ R`
  is linearly equivalent to `ι →₀ N`

* `TensorProduct.finsuppLeft'`, if `M` is an `S`-module,
  then the tensor product of `ι →₀ M` and `N` is `S`-linearly equivalent
  to `ι →₀ M ⊗[R] N`

* `finsuppTensorFinsupp`, the tensor product of `ι →₀ M` and `κ →₀ N`
  is linearly equivalent to `(ι × κ) →₀ (M ⊗ N)`.

-/

noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

section TensorProduct

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (N : Type*) [AddCommMonoid N] [Module R N]

namespace TensorProduct

variable (ι : Type*) [DecidableEq ι]

noncomputable def finsuppLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ M ⊗[R] N :=
  AlgebraTensorModule.congr (finsuppLEquivDirectSum S M ι) (.refl R N) ≪≫ₗ
    directSumLeft _ S (fun _ ↦ M) N ≪≫ₗ (finsuppLEquivDirectSum _ _ ι).symm

variable {R S M N ι}

lemma finsuppLeft_apply_tmul (p : ι →₀ M) (n : N) :
    finsuppLeft R S M N ι (p ⊗ₜ[R] n) = p.sum fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [add_tmul, map_add, hf, hg, Finsupp.sum_add_index]
  | single => simp [finsuppLeft]
