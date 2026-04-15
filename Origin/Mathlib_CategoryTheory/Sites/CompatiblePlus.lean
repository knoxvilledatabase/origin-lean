/-
Extracted from CategoryTheory/Sites/CompatiblePlus.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

In this file, we prove that the plus functor is compatible with functors which
preserve the correct limits and colimits.

See `CategoryTheory/Sites/CompatibleSheafification` for the compatibility
of sheafification, which follows easily from the content in this file.

-/

noncomputable section

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory Limits Opposite Functor

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {D : Type*} [Category* D]

variable {E : Type*} [Category* E]

variable (F : D ⥤ E)

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]

variable [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]

variable [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]

variable (P : Cᵒᵖ ⥤ D)

set_option backward.isDefEq.respectTransparency false in

def diagramCompIso (X : C) : J.diagram P X ⋙ F ≅ J.diagram (P ⋙ F) X :=
  NatIso.ofComponents
    (fun W => by
      refine ?_ ≪≫ HasLimit.isoOfNatIso (W.unop.multicospanComp _ _).symm
      refine
        (isLimitOfPreserves F (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _))
    (by
      intro A B f
      dsimp
      ext g
      simp [← F.map_comp])

set_option backward.isDefEq.respectTransparency false in
