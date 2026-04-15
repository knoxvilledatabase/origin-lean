/-
Extracted from Analysis/Normed/Operator/NormedSpace.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Operator norm for maps on normed spaces

This file contains statements about operator norm for which it really matters that the
underlying space has a norm (rather than just a seminorm).
-/

suppress_compilation

open Topology

open scoped NNReal

variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G : Type*}

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup Fₗ]

open Metric ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G] [NormedSpace 𝕜 Fₗ]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} (f : E →SL[σ₁₂] F)

namespace LinearMap

theorem bound_of_shell [RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜}
    (hc : 1 < ‖c‖) (hf : ∀ x, ε / ‖c‖ ≤ ‖x‖ → ‖x‖ < ε → ‖f x‖ ≤ C * ‖x‖) (x : E) :
    ‖f x‖ ≤ C * ‖x‖ := by
  by_cases hx : x = 0; · simp [hx]
  exact SemilinearMapClass.bound_of_shell_semi_normed f ε_pos hc hf (norm_ne_zero_iff.2 hx)

theorem antilipschitz_of_comap_nhds_le [h : RingHomIsometric σ₁₂] (f : E →ₛₗ[σ₁₂] F)
    (hf : (𝓝 0).comap f ≤ 𝓝 0) : ∃ K, AntilipschitzWith K f := by
  rcases ((nhds_basis_ball.comap _).le_basis_iff nhds_basis_ball).1 hf 1 one_pos with ⟨ε, ε0, hε⟩
  simp only [Set.subset_def, Set.mem_preimage, mem_ball_zero_iff] at hε
  lift ε to ℝ≥0 using ε0.le
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨ε⁻¹ * ‖c‖₊, AddMonoidHomClass.antilipschitz_of_bound f fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [← hx] at hf
    obtain rfl : x = 0 := Specializes.eq (specializes_iff_pure.2 <|
      ((Filter.tendsto_pure_pure _ _).mono_right (pure_le_nhds _)).le_comap.trans hf)
    exact norm_zero.trans_le (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))
  have hc₀ : c ≠ 0 := norm_pos_iff.1 (one_pos.trans hc)
  rw [← h.1] at hc
  rcases rescale_to_shell_zpow hc ε0 hx with ⟨n, -, hlt, -, hle⟩
  simp only [← map_zpow₀, h.1, ← map_smulₛₗ] at hlt hle
  calc
    ‖x‖ = ‖c ^ n‖⁻¹ * ‖c ^ n • x‖ := by
      rwa [← norm_inv, ← norm_smul, inv_smul_smul₀ (zpow_ne_zero _ _)]
    _ ≤ ‖c ^ n‖⁻¹ * 1 := by gcongr; exact (hε _ hlt).le
    _ ≤ ε⁻¹ * ‖c‖ * ‖f x‖ := by rwa [mul_one]

end LinearMap

namespace ContinuousLinearMap

section OpNorm

open Set Real

theorem opNorm_zero_iff [RingHomIsometric σ₁₂] : ‖f‖ = 0 ↔ f = 0 :=
  Iff.intro
    (fun hn => ContinuousLinearMap.ext fun x => norm_le_zero_iff.1
      (calc
        _ ≤ ‖f‖ * ‖x‖ := le_opNorm _ _
        _ = _ := by rw [hn, zero_mul]))
    (by
      rintro rfl
      exact opNorm_zero)

-- INSTANCE (free from Core): toNormedAddCommGroup

-- INSTANCE (free from Core): toNormedRing

theorem antilipschitz_of_isEmbedding (f : E →L[𝕜] Fₗ) (hf : IsEmbedding f) :
    ∃ K, AntilipschitzWith K f :=
  f.toLinearMap.antilipschitz_of_comap_nhds_le <| map_zero f ▸ (hf.nhds_eq_comap 0).ge

end OpNorm

end ContinuousLinearMap

namespace LinearIsometry
