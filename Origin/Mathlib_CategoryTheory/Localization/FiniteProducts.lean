/-
Extracted from CategoryTheory/Localization/FiniteProducts.lean
Genuine: 10 of 16 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-! The localized category has finite products

In this file, it is shown that if `L : C ⥤ D` is
a localization functor for `W : MorphismProperty C` and that
`W` is stable under finite products, then `D` has finite
products, and `L` preserves finite products.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  (W : MorphismProperty C) [L.IsLocalization W]

namespace HasProductsOfShapeAux

variable (J : Type) [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J]

lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [W.ContainsIdentities] [Finite J]

noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L W J ≅
      lim ⋙ L := by
  apply Localization.fac

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L W J :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)

lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L W J).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L W J).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app

noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cone.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

end HasProductsOfShapeAux

variable [W.ContainsIdentities]

include L

lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    [W.IsStableUnderProductsOfShape J] :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

lemma preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J] :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

include W in

lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _⟩

include W in

lemma preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves _ := preservesProductsOfShape L W _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): [W.HasLocalization]

-- INSTANCE (free from Core): [W.HasLocalization]

end Localization

end CategoryTheory
