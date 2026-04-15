/-
Extracted from CategoryTheory/Limits/Preserves/FunctorCategory.lean
Genuine: 2 of 11 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# Preservation of (co)limits in the functor category

* Show that if `X ⨯ -` preserves colimits in `D` for any `X : D`, then the product functor `F ⨯ -`
  for `F : C ⥤ D` preserves colimits.

  The idea of the proof is simply that products and colimits in the functor category are computed
  pointwise, so pointwise preservation implies general preservation.
* Show that `F ⋙ -` preserves limits if the target category has limits.
* Show that `F : C ⥤ D` preserves limits of a certain shape
  if `Lan F.op : Cᵒᵖ ⥤ Type*` preserves such limits.

## References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

universe w w' v v₁ v₂ v₃ u u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Limits Functor

variable {C : Type u} [Category.{v₁} C]

variable {D : Type u₂} [Category.{u} D]

variable {E : Type u} [Category.{v₂} E]

lemma FunctorCategory.prod_preservesColimits [HasBinaryProducts D] [HasColimits D]
    [∀ X : D, PreservesColimits (prod.functor.obj X)] (F : C ⥤ D) :
    PreservesColimits (prod.functor.obj F) where
  preservesColimitsOfShape {J : Type u} [Category.{u, u} J] :=
    {
      preservesColimit := fun {K : J ⥤ C ⥤ D} => ({
          preserves := fun {c : Cocone K} (t : IsColimit c) => ⟨by
            apply evaluationJointlyReflectsColimits _ fun {k} => ?_
            change IsColimit ((prod.functor.obj F ⋙ (evaluation _ _).obj k).mapCocone c)
            let this :=
              isColimitOfPreserves ((evaluation C D).obj k ⋙ prod.functor.obj (F.obj k)) t
            apply IsColimit.mapCoconeEquiv _ this
            apply (NatIso.ofComponents _ _).symm
            · intro G
              apply asIso (prodComparison ((evaluation C D).obj k) F G)
            · intro G G'
              apply prodComparison_natural ((evaluation C D).obj k) (𝟙 F)⟩ }) }

end

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

-- INSTANCE (free from Core): whiskeringLeft_preservesLimitsOfShape

-- INSTANCE (free from Core): whiskeringLeft_preservesColimitsOfShape

-- INSTANCE (free from Core): whiskeringLeft_preservesLimits

-- INSTANCE (free from Core): whiskeringLeft_preservesColimit

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): whiskeringRight_preservesLimitsOfShape

-- INSTANCE (free from Core): {C

-- INSTANCE (free from Core): {C

def limitCompWhiskeringRightIsoLimitComp {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] (G : J ⥤ C ⥤ D) :
    limit (G ⋙ (whiskeringRight _ _ _).obj F) ≅ limit G ⋙ F :=
  (preservesLimitIso _ _).symm

set_option backward.isDefEq.respectTransparency false in
