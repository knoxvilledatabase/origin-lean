/-
Extracted from CategoryTheory/Sites/Coherent/ExtensiveColimits.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# Colimits in categories of extensive sheaves

This file proves that `J`-shaped colimits of `A`-valued sheaves for the extensive topology are
computed objectwise if `colim : J ⥤ A ⥤ A` preserves finite products.

This holds for all shapes `J` if `A` is a preadditive category.

This can also easily be applied to filtered `J` in the case when `A` is a category of sets, and
eventually to sifted `J` once that API is developed.
-/

namespace CategoryTheory

open Limits Sheaf GrothendieckTopology Opposite

variable {A C J : Type*} [Category* A] [Category* C] [Category* J]
  [FinitaryExtensive C] [HasColimitsOfShape J A]

lemma isSheaf_pointwiseColimit [PreservesFiniteProducts (colim (J := J) (C := A))]
    (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (pointwiseCocone (G ⋙ sheafToPresheaf _ A)).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseCocone_pt]
  apply +allowSynthFailures comp_preservesFiniteProducts
  have : ∀ (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := fun i ↦ by
    rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]
    exact (G.obj i).property
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_evaluation _ _ fun d ↦
    inferInstanceAs (PreservesLimitsOfShape _ ((G ⋙ sheafToPresheaf _ _).obj d))⟩

-- INSTANCE (free from Core): [Preadditive

-- INSTANCE (free from Core): [PreservesFiniteProducts

-- INSTANCE (free from Core): [Preadditive

end

end CategoryTheory
