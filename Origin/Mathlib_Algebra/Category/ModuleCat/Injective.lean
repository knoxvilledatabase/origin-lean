/-
Extracted from Algebra/Category/ModuleCat/Injective.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Injective objects in the category of $R$-modules
-/

open CategoryTheory

universe u v

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

namespace Module

theorem injective_object_of_injective_module [inj : Injective R M] :
    CategoryTheory.Injective (ModuleCat.of R M) where
  factors g f m :=
    have ⟨l, h⟩ := inj.out f.hom ((ModuleCat.mono_iff_injective f).mp m) g.hom
    ⟨ModuleCat.ofHom l, by ext x; simpa using h x⟩

theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, h⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    obtain rfl := ModuleCat.hom_ext_iff.mp h
    exact ⟨l.hom, fun _ => rfl⟩

theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) :=
  ⟨fun _ => injective_object_of_injective_module R M,
   fun _ => injective_module_of_injective_object R M⟩

end Module

-- INSTANCE (free from Core): ModuleCat.ulift_injective_of_injective.{v'}
