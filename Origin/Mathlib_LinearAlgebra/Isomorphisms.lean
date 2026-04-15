/-
Extracted from LinearAlgebra/Isomorphisms.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `LinearMap.quotKerEquivRange`, `LinearMap.quotientInfEquivSupQuotient` and
  `Submodule.quotientQuotientEquivQuotient`.

-/

universe u v

variable {R M M₂ M₃ : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup M₂] [AddCommGroup M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f : M →ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/

namespace LinearMap

open Submodule

section IsomorphismLaws

noncomputable def quotKerEquivRange : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  (LinearEquiv.ofInjective ((LinearMap.ker f).liftQ f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _ (le_refl (LinearMap.ker f))).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftQ _ _ _)

noncomputable def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans <| .ofTop (LinearMap.range f) <| range_eq_top.2 hf
