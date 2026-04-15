/-
Extracted from CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean
Genuine: 4 of 9 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Continuity of functors from well-ordered types

Let `F : J ⥤ C` be a functor from a well-ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

-/

universe w w' v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J]

class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone F) :=
      (IsWellOrderContinuous.nonempty_isColimit m hm).some

noncomputable def isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous]
    {α : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) :
    IsColimit (f.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): {n

lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocone.ext (e.app _)))⟩

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): IsWellOrderContinuous.restriction_setIci

end CategoryTheory.Functor
