/-
Extracted from CategoryTheory/Sites/CompatibleSheafification.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor

open Opposite

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type*} [Category* D]

variable {E : Type*} [Category* E]

variable (F : D ⥤ E)

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]

variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

noncomputable def sheafifyCompIso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
  J.plusCompIso _ _ ≪≫ (J.plusFunctor _).mapIso (J.plusCompIso _ _)

noncomputable def sheafificationWhiskerLeftIso (P : Cᵒᵖ ⥤ D)
    [∀ (F : D ⥤ E) (X : C), PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
    [∀ (F : D ⥤ E) (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D),
        PreservesLimit (W.index P).multicospan F] :
    (whiskeringLeft _ _ E).obj (J.sheafify P) ≅
    (whiskeringLeft _ _ _).obj P ⋙ J.sheafification E := by
  refine J.plusFunctorWhiskerLeftIso _ ≪≫ ?_ ≪≫ associator _ _ _
  refine isoWhiskerRight ?_ _
  exact J.plusFunctorWhiskerLeftIso _

set_option backward.isDefEq.respectTransparency false in
