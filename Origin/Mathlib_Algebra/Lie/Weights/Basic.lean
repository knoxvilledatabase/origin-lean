/-
Extracted from Algebra/Lie/Weights/Basic.lean
Genuine: 12 of 13 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Weight spaces of Lie modules of nilpotent Lie algebras

Just as a key tool when studying the behaviour of a linear operator is to decompose the space on
which it acts into a sum of (generalised) eigenspaces, a key tool when studying a representation `M`
of Lie algebra `L` is to decompose `M` into a sum of simultaneous eigenspaces of `x` as `x` ranges
over `L`. These simultaneous generalised eigenspaces are known as the weight spaces of `M`.

When `L` is nilpotent, it follows from the binomial theorem that weight spaces are Lie submodules.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieModule.genWeightSpaceOf`
  * `LieModule.genWeightSpace`
  * `LieModule.Weight`
  * `LieModule.posFittingCompOf`
  * `LieModule.posFittingComp`
  * `LieModule.iSup_ucs_eq_genWeightSpace_zero`
  * `LieModule.iInf_lowerCentralSeries_eq_posFittingComp`
  * `LieModule.isCompl_genWeightSpace_zero_posFittingComp`
  * `LieModule.iSupIndep_genWeightSpace`
  * `LieModule.iSup_genWeightSpace_eq_top`

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 7--9*](bourbaki1975b)

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector
-/

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

open Set Function TensorProduct LieModule

variable (M) in

def weightSpace (χ : L → R) : LieSubmodule R L M where
  __ := ⨅ x : L, (toEnd R L M x).eigenspace (χ x)
  lie_mem {x m} hm := by simp_all [smul_comm (χ x)]

lemma mem_weightSpace (χ : L → R) (m : M) : m ∈ weightSpace M χ ↔ ∀ x, ⁅x, m⁆ = χ x • m := by
  simp [weightSpace]

section notation_genWeightSpaceOf

local notation3 "𝕎("M", " χ", " x")" => (toEnd R L M x).maxGenEigenspace χ

protected theorem weight_vector_multiplication (M₁ M₂ M₃ : Type*)
    [AddCommGroup M₁] [Module R M₁] [LieRingModule L M₁] [LieModule R L M₁] [AddCommGroup M₂]
    [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂] [AddCommGroup M₃] [Module R M₃]
    [LieRingModule L M₃] [LieModule R L M₃] (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : R) (x : L) :
    LinearMap.range ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (mapIncl 𝕎(M₁, χ₁, x) 𝕎(M₂, χ₂, x))) ≤
      𝕎(M₃, χ₁ + χ₂, x) := by
  -- Unpack the statement of the goal.
  intro m₃
  simp only [TensorProduct.mapIncl, LinearMap.mem_range, LinearMap.coe_comp,
    LieModuleHom.coe_toLinearMap, Function.comp_apply, exists_imp, Module.End.mem_maxGenEigenspace]
  rintro t rfl
  -- Set up some notation.
  let F : Module.End R M₃ := toEnd R L M₃ x - (χ₁ + χ₂) • ↑1
  -- The goal is linear in `t` so use induction to reduce to the case that `t` is a pure tensor.
  refine t.induction_on ?_ ?_ ?_
  · use 0; simp only [map_zero]
  swap
  · rintro t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩; use max k₁ k₂
    simp only [map_add, Module.End.pow_map_zero_of_le (le_max_left k₁ k₂) hk₁,
      Module.End.pow_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero]
  -- Now the main argument: pure tensors.
  rintro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩
  change ∃ k, (F ^ k) ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃) (m₁ ⊗ₜ m₂)) = (0 : M₃)
  -- Eliminate `g` from the picture.
  let f₁ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₁ x - χ₁ • ↑1).rTensor M₂
  let f₂ : Module.End R (M₁ ⊗[R] M₂) := (toEnd R L M₂ x - χ₂ • ↑1).lTensor M₁
  have h_comm_square : F ∘ₗ ↑g = (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp (f₁ + f₂) := by
    ext m₁ m₂
    simp only [f₁, f₂, F, ← g.map_lie x (m₁ ⊗ₜ m₂), add_smul, sub_tmul, tmul_sub, smul_tmul,
      lie_tmul_right, tmul_smul, toEnd_apply_apply, map_smul, Module.End.one_apply,
      LieModuleHom.coe_toLinearMap, LinearMap.smul_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply,
      LinearMap.lTensor_tmul, AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
    abel
  rsuffices ⟨k, hk⟩ : ∃ k : ℕ, ((f₁ + f₂) ^ k) (m₁ ⊗ₜ m₂) = 0
  · use k
    change (F ^ k) (g.toLinearMap (m₁ ⊗ₜ[R] m₂)) = 0
    rw [← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute h_comm_square,
      LinearMap.comp_apply, hk, map_zero]
  -- Unpack the information we have about `m₁`, `m₂`.
  simp only [Module.End.mem_maxGenEigenspace] at hm₁ hm₂
  obtain ⟨k₁, hk₁⟩ := hm₁
  obtain ⟨k₂, hk₂⟩ := hm₂
  have hf₁ : (f₁ ^ k₁) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₁, hk₁, zero_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_pow]
  have hf₂ : (f₂ ^ k₂) (m₁ ⊗ₜ m₂) = 0 := by
    simp only [f₂, hk₂, tmul_zero, LinearMap.lTensor_tmul, LinearMap.lTensor_pow]
  -- It's now just an application of the binomial theorem.
  use k₁ + k₂ - 1
  have hf_comm : Commute f₁ f₂ := by
    ext m₁ m₂
    simp only [f₁, f₂, Module.End.mul_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      AlgebraTensorModule.curry_apply, LinearMap.lTensor_tmul, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars]
  rw [hf_comm.add_pow']
  simp only [Finset.sum_apply, LinearMap.coe_sum, LinearMap.smul_apply]
  -- The required sum is zero because each individual term is zero.
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  -- Eliminate the binomial coefficients from the picture.
  suffices (f₁ ^ i * f₂ ^ j) (m₁ ⊗ₜ m₂) = 0 by rw [this]; apply smul_zero
  -- Finish off with appropriate case analysis.
  rcases Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi | hj
  · rw [(hf_comm.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hf₁,
      map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hf₂, map_zero]

lemma lie_mem_maxGenEigenspace_toEnd
    {χ₁ χ₂ : R} {x y : L} {m : M} (hy : y ∈ 𝕎(L, χ₁, x)) (hm : m ∈ 𝕎(M, χ₂, x)) :
    ⁅y, m⁆ ∈ 𝕎(M, χ₁ + χ₂, x) := by
  apply LieModule.weight_vector_multiplication L M M (toModuleHom R L M) χ₁ χ₂
  simp only [LieModuleHom.coe_toLinearMap, Function.comp_apply, LinearMap.coe_comp,
    TensorProduct.mapIncl, LinearMap.mem_range]
  use ⟨y, hy⟩ ⊗ₜ ⟨m, hm⟩
  simp only [Submodule.subtype_apply, toModuleHom_apply, TensorProduct.map_tmul]

variable (M)

def genWeightSpaceOf [LieRing.IsNilpotent L] (χ : R) (x : L) : LieSubmodule R L M :=
  { 𝕎(M, χ, x) with
    lie_mem := by
      intro y m hm
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid] at hm ⊢
      rw [← zero_add χ]
      exact lie_mem_maxGenEigenspace_toEnd (by simp) hm }

end notation_genWeightSpaceOf

variable (M)

variable [LieRing.IsNilpotent L]

theorem mem_genWeightSpaceOf (χ : R) (x : L) (m : M) :
    m ∈ genWeightSpaceOf M χ x ↔ ∃ k : ℕ, ((toEnd R L M x - χ • ↑1) ^ k) m = 0 := by
  simp [genWeightSpaceOf]

theorem coe_genWeightSpaceOf_zero (x : L) :
    ↑(genWeightSpaceOf M (0 : R) x) = ⨆ k, LinearMap.ker (toEnd R L M x ^ k) := by
  simp [genWeightSpaceOf, ← Module.End.iSup_genEigenspace_eq]

def genWeightSpace (χ : L → R) : LieSubmodule R L M :=
  ⨅ x, genWeightSpaceOf M (χ x) x

theorem mem_genWeightSpace (χ : L → R) (m : M) :
    m ∈ genWeightSpace M χ ↔ ∀ x, ∃ k : ℕ, ((toEnd R L M x - χ x • ↑1) ^ k) m = 0 := by
  simp [genWeightSpace, mem_genWeightSpaceOf]

lemma genWeightSpace_le_genWeightSpaceOf (x : L) (χ : L → R) :
    genWeightSpace M χ ≤ genWeightSpaceOf M (χ x) x :=
  iInf_le _ x

lemma weightSpace_le_genWeightSpace (χ : L → R) :
    weightSpace M χ ≤ genWeightSpace M χ := by
  apply le_iInf
  intro x
  rw [← (LieSubmodule.toSubmodule_orderEmbedding R L M).le_iff_le]
  apply (iInf_le _ x).trans
  exact ((toEnd R L M x).genEigenspace (χ x)).monotone le_top

variable (R L) in

structure Weight where
  /-- The family of eigenvalues corresponding to a weight. -/
  toFun : L → R
  genWeightSpace_ne_bot' : genWeightSpace M toFun ≠ ⊥

namespace Weight

-- INSTANCE (free from Core): instFunLike
