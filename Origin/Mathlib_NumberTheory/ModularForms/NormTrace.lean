/-
Extracted from NumberTheory/ModularForms/NormTrace.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Norm and trace maps

Given two subgroups `𝒢, ℋ` of `GL(2, ℝ)` with `𝒢.relindex ℋ ≠ 0` (i.e. `𝒢 ⊓ ℋ` has finite index
in `ℋ`), we define a trace map from `ModularForm (𝒢 ⊓ ℋ) k` to `ModularForm ℋ k`.
-/

open UpperHalfPlane

open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒢 k]

def quotientFunc (q : 𝒬) (τ : ℍ) : ℂ :=
  q.liftOn (fun g ↦ ((f : ℍ → ℂ) ∣[k] g.val⁻¹) τ) (fun h h' hhh' ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ g ∈ 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])
