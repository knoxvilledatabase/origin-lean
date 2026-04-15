/-
Extracted from LinearAlgebra/Quotient/Bilinear.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lifting bilinear forms to quotients
-/

namespace LinearMap

section Asymmetric -- "asymmetric" case of a form `M × N → P`

variable {R R₂ S S₂ M N P : Type*} [Ring R] [Ring R₂] [Ring S] [Ring S₂]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module S N] [Module R₂ P]
    [Module S₂ P] [SMulCommClass R₂ S₂ P] {ρ : R →+* R₂} {σ : S →+* S₂}

attribute [local instance] SMulCommClass.symm

def liftQ₂ (M' : Submodule R M) (N' : Submodule S N) (f : M →ₛₗ[ρ] N →ₛₗ[σ] P)
    (hM' : M' ≤ f.ker) (hN' : N' ≤ f.flip.ker) :
    M ⧸ M' →ₛₗ[ρ] N ⧸ N' →ₛₗ[σ] P :=
  have : ∀ n ∈ N', n ∈ (M'.liftQ f hM').flip.ker := fun n hn ↦ by
    simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply, Submodule.Quotient.forall,
      Submodule.liftQ_apply, ← f.flip_apply, show f.flip n = 0 from hN' hn, LinearMap.zero_apply,
      forall_true_iff]
  (N'.liftQ (M'.liftQ f hM').flip this).flip
