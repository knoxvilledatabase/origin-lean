/-
Extracted from Analysis/LocallyConvex/ContinuousOfBounded.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Continuity and Von Neumann boundedness

This file proves that for two topological vector spaces `E` and `F` over nontrivially normed fields,
if `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous
(this is `LinearMap.continuous_of_locally_bounded`).

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

open TopologicalSpace Bornology Filter Topology Pointwise

variable {𝕜 𝕜' E F : Type*}

variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

variable [AddCommGroup F] [TopologicalSpace F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

variable [NormedField 𝕜'] [Module 𝕜' F]

variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

def LinearMap.clmOfExistsBoundedImage [IsTopologicalAddGroup F] (f : E →ₛₗ[σ] F)
    (h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)) : E →SL[σ] F :=
  ⟨f, by
    -- It suffices to show that `f` is continuous at `0`.
    refine continuous_of_continuousAt_zero f ?_
    rw [continuousAt_def, f.map_zero]
    intro U hU
    -- Continuity means that `U ∈ 𝓝 0` implies that `f ⁻¹' U ∈ 𝓝 0`.
    rcases h with ⟨V, hV, h⟩
    rcases (h hU).exists_pos with ⟨r, hr, h⟩
    rcases NormedField.exists_lt_norm 𝕜 r with ⟨x, hx⟩
    specialize h (σ x) (by simpa using hx.le)
    -- After unfolding all the definitions, we know that `f '' V ⊆ σ x • U`. We use this to show the
    -- inclusion `x⁻¹ • V ⊆ f⁻¹' U`.
    have x_ne := norm_pos_iff.mp (hr.trans hx)
    have : x⁻¹ • V ⊆ f ⁻¹' U :=
      calc
        x⁻¹ • V ⊆ x⁻¹ • f ⁻¹' (f '' V) := Set.smul_set_mono (Set.subset_preimage_image (⇑f) V)
        _ ⊆ x⁻¹ • f ⁻¹' (σ x • U) := Set.smul_set_mono (Set.preimage_mono h)
        _ = f ⁻¹' U := by rw [x_ne.isUnit.preimage_smul_setₛₗ _, inv_smul_smul₀ x_ne _]
    -- Using this inclusion, it suffices to show that `x⁻¹ • V` is in `𝓝 0`, which is trivial.
    grw [← this]
    rwa [set_smul_mem_nhds_zero_iff (inv_ne_zero x_ne)]⟩
