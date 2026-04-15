/-
Extracted from CategoryTheory/EffectiveEpi/Extensive.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Preserving and reflecting effective epis on extensive categories

We prove that a functor between `FinitaryPreExtensive` categories preserves (resp. reflects) finite
effective epi families if it preserves (resp. reflects) effective epis.
-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [FinitaryPreExtensive C]

theorem effectiveEpi_desc_iff_effectiveEpiFamily {α : Type} [Finite α]
    {B : C} (X : α → C) (π : (a : α) → X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h ↦ ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g ↦
    (FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a ↦ Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ ↦ inferInstance⟩

variable {D : Type*} [Category* D] [FinitaryPreExtensive D]

variable (F : C ⥤ D) [PreservesFiniteCoproducts F]

-- INSTANCE (free from Core): [F.ReflectsEffectiveEpis]

-- INSTANCE (free from Core): [F.PreservesEffectiveEpis]

end CategoryTheory
