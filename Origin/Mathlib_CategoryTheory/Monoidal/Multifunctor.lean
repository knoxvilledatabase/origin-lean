/-
Extracted from CategoryTheory/Monoidal/Multifunctor.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Constructing monoidal functors from natural transformations between multifunctors

This file provides alternative constructors for (op/lax) monoidal functors, given tensorators
`μ : F - ⊗ F - ⟶  F (- ⊗ -)` / `δ : F (- ⊗ -) ⟶ F - ⊗ F -` as natural transformations between
bifunctors. The associativity conditions are phrased as equalities of natural transformations
between trifunctors `(F - ⊗ F -) ⊗ F - ⟶ F (- ⊗ (- ⊗ -))` / `F ((- ⊗ -) ⊗ -) ⟶ F - ⊗ (F - ⊗ F -)`,
and the unitality conditions are phrased as equalities of natural transformation between functors.

Once we have more API for quadrifunctors, we can add constructors for monoidal category structures
by phrasing the pentagon axiom as an equality of natural transformations between quadrifunctors.
-/

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {D : Type*} [Category* D] [MonoidalCategory D]

namespace MonoidalCategory

open Functor

abbrev curriedTensorInsertFunctor₁ (F : C ⥤ D) : C ⥤ D ⥤ D :=
  (((whiskeringLeft₂ _).obj F).obj (𝟭 D)).obj (curriedTensor D)

abbrev curriedTensorInsertFunctor₂ (F : C ⥤ D) : D ⥤ C ⥤ D :=
  (((whiskeringLeft₂ _).obj (𝟭 D)).obj F).obj (curriedTensor D)

abbrev curriedTensorPre (F : C ⥤ D) : C ⥤ C ⥤ D :=
  (whiskeringLeft₂ _).obj F |>.obj F |>.obj (curriedTensor D)

abbrev curriedTensorPost (F : C ⥤ D) : C ⥤ C ⥤ D :=
  (Functor.postcompose₂.obj F).obj (curriedTensor C)

abbrev curriedTensorPrePre (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensorPre F) (curriedTensorInsertFunctor₂ F)

abbrev curriedTensorPrePre' (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorInsertFunctor₁ F) (curriedTensorPre F)

abbrev curriedTensorPostPre (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensor C) (curriedTensorPre F)

abbrev curriedTensorPrePost (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorPre F) (curriedTensor C)

abbrev curriedTensorPostPost (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₁₂ (curriedTensor C) (curriedTensorPost F)

abbrev curriedTensorPostPost' (F : C ⥤ D) : C ⥤ C ⥤ C ⥤ D :=
  bifunctorComp₂₃ (curriedTensorPost F) (curriedTensor C)
