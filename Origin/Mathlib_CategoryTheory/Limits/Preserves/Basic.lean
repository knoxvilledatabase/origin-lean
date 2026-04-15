/-
Extracted from CategoryTheory/Limits/Preserves/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C ⥤ D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/

open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cone K} (hc : IsLimit c) : Nonempty (IsLimit (F.mapCone c))

class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop where
  preserves {c : Cocone K} (hc : IsColimit c) : Nonempty (IsColimit (F.mapCocone c))

class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by infer_instance

class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) : Prop where
  preservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by infer_instance
