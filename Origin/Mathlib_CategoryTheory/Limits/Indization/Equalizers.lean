/-
Extracted from CategoryTheory/Limits/Indization/Equalizers.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits

/-!
# Equalizers of ind-objects

The eventual goal of this file is to show that if a category `C` has equalizers, then ind-objects
are closed under equalizers. For now, it contains one of the main prerequisites, namely we show
that under sufficient conditions the limit of a diagram in `I ⥤ C` taken in `Cᵒᵖ ⥤ Type v` is an
ind-object.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 6.1
-/

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {I : Type v} [SmallCategory I] [IsFiltered I]

variable {J : Type} [SmallCategory J] [FinCategory J]

variable (F : J ⥤ I ⥤ C)

theorem isIndObject_limit_comp_yoneda_comp_colim
    (hF : ∀ i, IsIndObject (limit (F.flip.obj i ⋙ yoneda))) :
    IsIndObject (limit (F ⋙ (whiskeringRight _ _ _).obj yoneda ⋙ colim)) := by
  let G : J ⥤ I ⥤ (Cᵒᵖ ⥤ Type v) := F ⋙ (whiskeringRight _ _ _).obj yoneda
  apply IsIndObject.map (HasLimit.isoOfNatIso (colimitFlipIsoCompColim G)).hom
  apply IsIndObject.map (colimitLimitIso G).hom
  apply isIndObject_colimit
  exact fun i => IsIndObject.map (limitObjIsoLimitCompEvaluation _ _).inv (hF i)

end

end CategoryTheory.Limits
