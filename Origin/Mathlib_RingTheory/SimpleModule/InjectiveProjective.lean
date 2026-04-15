/-
Extracted from RingTheory/SimpleModule/InjectiveProjective.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
If `R` is a semisimple ring, then any `R`-module is both injective and projective.

-/

namespace Module

variable (R : Type*) [Ring R] [IsSemisimpleRing R] (M : Type*) [AddCommGroup M] [Module R M]

theorem injective_of_isSemisimpleRing : Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let ⟨h, comp⟩ := IsSemisimpleModule.extension_property f hf g
    ⟨h, fun _ ↦ by rw [← comp, LinearMap.comp_apply]⟩

theorem projective_of_isSemisimpleRing : Module.Projective R M :=
  .of_lifting_property'' (IsSemisimpleModule.lifting_property · · _)

end Module
