/-
Extracted from RingTheory/Regular/Category.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Categorical constructions for `IsSMulRegular`
-/

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Ideal Pointwise

lemma LinearMap.exact_smul_id_smul_top_mkQ (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (r • LinearMap.id : M →ₗ[R] M) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]

namespace ModuleCat
