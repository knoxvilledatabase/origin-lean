/-
Extracted from Analysis/InnerProductSpace/Projection/Reflection.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Reflection

A linear isometry equivalence `K.reflection : E ≃ₗᵢ[𝕜] E` in constructed, by choosing
for each `u : E`, `K.reflection u = 2 • K.starProjection u - u`.
-/

noncomputable section

namespace Submodule

section reflection

open Submodule RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)

variable [K.HasOrthogonalProjection]

def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

def reflection : E ≃ₗᵢ[𝕜] E :=
  { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjection x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this using 2
      · dsimp [reflectionLinearEquiv, v, w]
        abel
      · simp only [v, add_sub_cancel] }

variable {K}
