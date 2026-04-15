/-
Extracted from CategoryTheory/EffectiveEpi/Preserves.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Functors preserving effective epimorphisms

This file concerns functors which preserve and/or reflect effective epimorphisms and effective
epimorphic families.

## TODO
- Find nice sufficient conditions in terms of preserving/reflecting (co)limits, to preserve/reflect
  effective epis, similar to `CategoryTheory.preserves_epi_of_preservesColimit`.
-/

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]

noncomputable section Equivalence

variable {D : Type*} [Category* D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))

set_option backward.isDefEq.respectTransparency false in

variable [EffectiveEpiFamily X π]

set_option backward.isDefEq.respectTransparency false in

def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a ↦ e.functor.obj (X a))
    (fun a ↦ e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map, Iso.inv_hom_id_app, Category.comp_id] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a ↦ ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

-- INSTANCE (free from Core): (F

example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [F.IsEquivalence] [EffectiveEpi π] :

    EffectiveEpi <| F.map π := inferInstance

end Equivalence

namespace Functor

variable {D : Type*} [Category* D]

section Preserves

class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

-- INSTANCE (free from Core): map_effectiveEpi

-- INSTANCE (free from Core): [IsRegularEpiCategory
