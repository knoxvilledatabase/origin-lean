/-
Extracted from CategoryTheory/Limits/Over.lean
Genuine: 4 of 12 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Limits and colimits in the over and under categories

Show that the forgetful functor `forget X : Over X ⥤ C` creates colimits, and hence `Over X` has
any colimits that `C` has (as well as the dual that `forget X : Under X ⟶ C` creates limits).

Note that the folder `CategoryTheory.Limits.Shapes.Constructions.Over` further shows that
`forget X : Over X ⥤ C` creates connected limits (so `Over X` has connected limits), and that
`Over X` has `J`-indexed products if `C` has `J`-indexed wide pullbacks.
-/

noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Over

-- INSTANCE (free from Core): hasColimit_of_hasColimit_comp_forget

-- INSTANCE (free from Core): [HasColimitsOfShape

-- INSTANCE (free from Core): [HasFiniteColimits

-- INSTANCE (free from Core): [HasColimits

-- INSTANCE (free from Core): [HasFiniteCoproducts

-- INSTANCE (free from Core): createsColimitsOfSize

example [HasColimits C] : PreservesColimits (forget X) :=

  inferInstance

example : ReflectsColimits (forget X) :=

  inferInstance

set_option backward.isDefEq.respectTransparency false in

theorem epi_left_of_epi [HasPushouts C] {f g : Over X} (h : f ⟶ g) [Epi h] : Epi h.left :=
  CostructuredArrow.epi_left_of_epi _

theorem epi_iff_epi_left [HasPushouts C] {f g : Over X} (h : f ⟶ g) : Epi h ↔ Epi h.left :=
  CostructuredArrow.epi_iff_epi_left _

-- INSTANCE (free from Core): createsColimitsOfSizeMapCompForget

-- INSTANCE (free from Core): preservesColimitsOfSize_map

def isColimitToOver {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsColimit c.toOver :=
  isColimitOfReflects (forget c.pt) <| IsColimit.equivIsoColimit c.mapCoconeToOver.symm hc

def _root_.CategoryTheory.Limits.colimit.isColimitToOver (F : J ⥤ C) [HasColimit F] :
    IsColimit (colimit.toOver F) :=
  Over.isColimitToOver (colimit.isColimit F)
