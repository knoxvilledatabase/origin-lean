/-
Extracted from RingTheory/Jacobson/Semiprimary.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Semiprimary rings

## Main definition

* `IsSemiprimaryRing R`: a ring `R` is semiprimary if
  `Ring.jacobson R` is nilpotent and `R ⧸ Ring.jacobson R` is semisimple.
-/

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]

variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]

variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]

theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ :=
  le_bot_iff.mp <| sInf_le isCoatom_bot

theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] :
    Module.jacobson R M = ⊥ :=
  have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M →ₗ[R] ∀ m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i ↦ IsSimpleModule.jacobson_eq_bot R _)

theorem IsSemisimpleRing.jacobson_eq_bot [IsSemisimpleRing R] : Ring.jacobson R = ⊥ :=
  IsSemisimpleModule.jacobson_eq_bot R R

theorem IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] (f : M →ₛₗ[τ₁₂] M₂) :
    Module.jacobson R M ≤ LinearMap.ker f :=
  (Module.le_comap_jacobson f).trans <| by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

theorem IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] :
    Ring.jacobson R ≤ Module.annihilator R M :=
  fun r hr ↦ Module.mem_annihilator.mpr fun m ↦ by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

-- INSTANCE (free from Core): (priority
