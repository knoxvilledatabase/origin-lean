/-
Extracted from CategoryTheory/Action/Limits.lean
Genuine: 8 of 37 | Dissolved: 0 | Infrastructure: 29
-/
import Origin.Core

/-!
# Categorical properties of `Action V G`

We show:

* When `V` has (co)limits so does `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
* The forgetful functor `Action V G ⥤ V` preserves any (co)limit whose image in `V` exists,
  and reflects all (co)limits.
-/

universe u v w₁ w₂ t₁ t₂

open CategoryTheory Limits

variable {V : Type*} [Category* V] {G : Type*} [Monoid G]

namespace Action

section Limits

-- INSTANCE (free from Core): [HasFiniteProducts

-- INSTANCE (free from Core): [HasFiniteLimits

-- INSTANCE (free from Core): [HasLimits

-- INSTANCE (free from Core): hasLimitsOfShape

-- INSTANCE (free from Core): [HasFiniteCoproducts

-- INSTANCE (free from Core): [HasFiniteColimits

-- INSTANCE (free from Core): [HasColimits

-- INSTANCE (free from Core): hasColimitsOfShape

end Limits

section Preservation

variable {C : Type*} [Category* C]

private lemma SingleObj.preservesLimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesLimit K F := by
  apply preservesLimit_of_evaluation
  intro _
  exact h

lemma preservesLimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesLimit K (F ⋙ Action.forget V G)) : PreservesLimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesLimit K F' := SingleObj.preservesLimit _ _ h
  apply preservesLimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

lemma preservesLimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesLimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesLimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesLimit_of_preserves
  exact PreservesLimitsOfShape.preservesLimit

lemma preservesLimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesLimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesLimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesLimitsOfShape_of_preserves
  exact PreservesLimitsOfSize.preservesLimitsOfShape

private lemma SingleObj.preservesColimit (F : C ⥤ SingleObj G ⥤ V)
    {J : Type*} [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ (evaluation (SingleObj G) V).obj (SingleObj.star G))) :
    PreservesColimit K F := by
  apply preservesColimit_of_evaluation
  intro _
  exact h

lemma preservesColimit_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (K : J ⥤ C)
    (h : PreservesColimit K (F ⋙ Action.forget V G)) : PreservesColimit K F := by
  let F' : C ⥤ SingleObj G ⥤ V := F ⋙ (Action.functorCategoryEquivalence V G).functor
  have : PreservesColimit K F' := SingleObj.preservesColimit _ _ h
  apply preservesColimit_of_reflects_of_preserves F (Action.functorCategoryEquivalence V G).functor

lemma preservesColimitsOfShape_of_preserves (F : C ⥤ Action V G) {J : Type*}
    [Category* J] (h : PreservesColimitsOfShape J (F ⋙ Action.forget V G)) :
    PreservesColimitsOfShape J F := by
  constructor
  intro K
  apply Action.preservesColimit_of_preserves
  exact PreservesColimitsOfShape.preservesColimit

lemma preservesColimitsOfSize_of_preserves (F : C ⥤ Action V G)
    (h : PreservesColimitsOfSize.{w₂, w₁} (F ⋙ Action.forget V G)) :
    PreservesColimitsOfSize.{w₂, w₁} F := by
  constructor
  intro J _
  apply Action.preservesColimitsOfShape_of_preserves
  exact PreservesColimitsOfSize.preservesColimitsOfShape

end Preservation

section Forget

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): [HasFiniteLimits

-- INSTANCE (free from Core): [HasFiniteColimits

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): {J

-- INSTANCE (free from Core): :

end Forget

namespace Functor

variable {W : Type*} [Category* W] (F : V ⥤ W) (G : Type*) [Monoid G] {J : Type*} [Category* J]

-- INSTANCE (free from Core): mapActionPreservesLimit_of_preserves

-- INSTANCE (free from Core): mapActionPreservesLimitsOfShapeOfPreserves

-- INSTANCE (free from Core): preservesLimitsOfSize_of_preserves

-- INSTANCE (free from Core): [PreservesFiniteLimits

-- INSTANCE (free from Core): mapActionPreservesColimit_of_preserves

-- INSTANCE (free from Core): mapActionPreservesColimitsOfShapeOfPreserves

-- INSTANCE (free from Core): preservesColimitsOfSize_of_preserves

-- INSTANCE (free from Core): [PreservesFiniteColimits

end Functor

section HasZeroMorphisms

variable [HasZeroMorphisms V]

-- INSTANCE (free from Core): {X
