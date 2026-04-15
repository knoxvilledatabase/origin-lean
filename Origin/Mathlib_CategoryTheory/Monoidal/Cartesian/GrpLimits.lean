/-
Extracted from CategoryTheory/Monoidal/Cartesian/GrpLimits.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Limits in `Grp C`

We show that `Grp C` has limits.
-/

namespace CategoryTheory

open Functor Grp Limits MonObj

universe w v

variable {C : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
  {J : Type w} [Category J] [HasLimitsOfShape J C]

-- INSTANCE (free from Core): :

noncomputable def Grp.limitAux (F : J ⥤ Grp C) : Grp C where
  X := (limit (F ⋙ forget₂Mon C)).X
  grp := GrpObj.ofInvertible (limit (F ⋙ forget₂Mon C)).X fun X f ↦
    letI e := Shrink.mulEquiv.symm.trans <| Iso.monCatIsoToMulEquiv <|
      preservesLimitIso (shrinkYonedaMon ⋙ (evaluation _ _).obj (.op X))
      (F ⋙ forget₂Mon C) ≪≫ (preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).symm
    letI := (limit (F ⋙ shrinkYonedaGrp.{max w v} ⋙ (evaluation _ _).obj (.op X))).str
    ((invertibleOfGroup (e f)).map e.symm).copy f (e.symm_apply_apply f).symm

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end CategoryTheory
