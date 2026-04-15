/-
Extracted from CategoryTheory/Limits/Shapes/FiniteLimits.lean
Genuine: 6 of 29 | Dissolved: 0 | Infrastructure: 23
-/
import Origin.Core

/-!
# Categories with finite limits.

A typeclass for categories with all finite (co)limits.
-/

universe w' w v' u' v u

noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

class HasFiniteLimits : Prop where
  /-- `C` has all limits over any type `J` whose objects and morphisms lie in the same universe
  and which has `FinType` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasLimitsOfShape J 𝒥 C _

-- INSTANCE (free from Core): (priority

lemma hasFiniteLimits_of_hasLimitsOfSize [HasLimitsOfSize.{v', u'} C] :
    HasFiniteLimits C where
  out := fun J hJ hJ' =>
    haveI := hasLimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasLimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (J

class HasFiniteColimits : Prop where
  /-- `C` has all colimits over any type `J` whose objects and morphisms lie in the same universe
  and which has `Fintype` objects and morphisms -/
  out (J : Type) [𝒥 : SmallCategory J] [@FinCategory J 𝒥] : @HasColimitsOfShape J 𝒥 C _

-- INSTANCE (free from Core): (priority

lemma hasFiniteColimits_of_hasColimitsOfSize [HasColimitsOfSize.{v', u'} C] :
    HasFiniteColimits C where
  out := fun J hJ hJ' =>
    haveI := hasColimitsOfSizeShrink.{0, 0} C
    let F := @FinCategory.equivAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ'
    @hasColimitsOfShape_of_equivalence (@FinCategory.AsType J (@FinCategory.fintypeObj J hJ hJ'))
    (@FinCategory.categoryAsType J (@FinCategory.fintypeObj J hJ hJ') hJ hJ') _ _ J hJ F _

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

open WalkingParallelPair WalkingParallelPairHom

-- INSTANCE (free from Core): fintypeWalkingParallelPair

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

-- INSTANCE (free from Core): instFintypeWalkingParallelPairHom

end

-- INSTANCE (free from Core): :

example [HasFiniteLimits C] : HasEqualizers C := by infer_instance

example [HasFiniteColimits C] : HasCoequalizers C := by infer_instance

variable {J : Type v}

namespace WidePullbackShape

-- INSTANCE (free from Core): fintypeObj

-- INSTANCE (free from Core): fintypeHom

end WidePullbackShape

namespace WidePushoutShape

-- INSTANCE (free from Core): fintypeObj

-- INSTANCE (free from Core): fintypeHom

end WidePushoutShape

-- INSTANCE (free from Core): finCategoryWidePullback

-- INSTANCE (free from Core): finCategoryWidePushout

class HasFiniteWidePullbacks : Prop where
  /-- `C` has all wide pullbacks for any Finite `J` -/
  out (J : Type) [Finite J] : HasLimitsOfShape (WidePullbackShape J) C

-- INSTANCE (free from Core): hasLimitsOfShape_widePullbackShape

class HasFiniteWidePushouts : Prop where
  /-- `C` has all wide pushouts for any Finite `J` -/
  out (J : Type) [Finite J] : HasColimitsOfShape (WidePushoutShape J) C

-- INSTANCE (free from Core): hasColimitsOfShape_widePushoutShape

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): fintypeWalkingPair

example [HasFiniteWidePullbacks C] : HasPullbacks C := by infer_instance

example [HasFiniteWidePushouts C] : HasPushouts C := by infer_instance

end CategoryTheory.Limits
