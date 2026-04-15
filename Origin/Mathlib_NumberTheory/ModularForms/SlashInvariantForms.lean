/-
Extracted from NumberTheory/ModularForms/SlashInvariantForms.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Slash invariant forms

This file defines functions that are invariant under a `SlashAction` which forms the basis for
defining `ModularForm` and `CuspForm`. We prove several instances for such spaces, in particular
that they form a module over `ℝ`, and over `ℂ` if the group is contained in `SL(2, ℝ)`.
-/

open Complex UpperHalfPlane ModularForm

open scoped MatrixGroups

noncomputable section

section SlashInvariantForms

open ModularForm

variable (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)

structure SlashInvariantForm where
  /-- The underlying function `ℍ → ℂ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun

class SlashInvariantFormClass [FunLike F ℍ ℂ] : Prop where
  slash_action_eq : ∀ (f : F), ∀ γ ∈ Γ, (f : ℍ → ℂ) ∣[k] γ = f

-- INSTANCE (free from Core): (priority

def SlashInvariantForm.Simps.coe (f : SlashInvariantForm Γ k) : ℍ → ℂ := f

initialize_simps_projections SlashInvariantForm (toFun → coe, as_prefix coe)

-- INSTANCE (free from Core): (priority

variable {F Γ k}
