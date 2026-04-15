/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Preorder.lean
Genuine: 2 of 7 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Preservation of well order continuous functors

Given a well-ordered type `J` and a functor `G : C ⥤ D`,
we define a type class `PreservesWellOrderContinuousOfShape J G`
saying that `G` preserves colimits of shape `Set.Iio j`
for any limit element `j : J`. It follows that if
`F : J ⥤ C` is well order continuous, then so is `F ⋙ G`.

-/

universe w w' v v' v'' u' u u''

namespace CategoryTheory

namespace Limits

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  (J : Type w) [LinearOrder J]

class PreservesWellOrderContinuousOfShape (G : C ⥤ D) : Prop where
  preservesColimitsOfShape (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G := by infer_instance

variable {J} in

lemma preservesColimitsOfShape_of_preservesWellOrderContinuousOfShape (G : C ⥤ D)
    [PreservesWellOrderContinuousOfShape J G]
    (j : J) (hj : Order.IsSuccLimit j) :
    PreservesColimitsOfShape (Set.Iio j) G :=
  PreservesWellOrderContinuousOfShape.preservesColimitsOfShape j hj

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (G₁

-- INSTANCE (free from Core): [HasIterationOfShape

-- INSTANCE (free from Core): [HasIterationOfShape

-- INSTANCE (free from Core): [HasIterationOfShape

end Limits

end CategoryTheory
