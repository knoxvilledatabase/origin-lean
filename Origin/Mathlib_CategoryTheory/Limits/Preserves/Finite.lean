/-
Extracted from CategoryTheory/Limits/Preserves/Finite.lean
Genuine: 20 of 48 | Dissolved: 0 | Infrastructure: 28
-/
import Origin.Core

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts` :
  see `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`.
  Also provides the dual version.
* `CategoryTheory.Limits.preservesFiniteLimitsIffFlat` :
  see `Mathlib/CategoryTheory/Functor/Flat.lean`.

-/

open CategoryTheory

namespace CategoryTheory.Limits

universe u w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E]

variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

class PreservesFiniteLimits (F : C ⥤ D) : Prop where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance

attribute [instance] PreservesFiniteLimits.preservesFiniteLimits

-- INSTANCE (free from Core): (priority

lemma PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

attribute [local instance] uliftCategory in

lemma comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

lemma preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_natIso h

class PreservesFiniteProducts (F : C ⥤ D) : Prop where
  preserves : ∀ n, PreservesLimitsOfShape (Discrete (Fin n)) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): comp_preservesFiniteProducts

-- INSTANCE (free from Core): (F

class ReflectsFiniteLimits (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteLimits.reflects

class ReflectsFiniteProducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsLimitsOfShape (Discrete (Fin n)) F

-- INSTANCE (free from Core): (priority

lemma ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

lemma preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G

lemma preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ := preservesLimitsOfShape_of_reflects_of_preserves F G

-- INSTANCE (free from Core): reflectsFiniteLimits_of_reflectsIsomorphisms

-- INSTANCE (free from Core): reflectsFiniteProducts_of_reflectsIsomorphisms

-- INSTANCE (free from Core): comp_reflectsFiniteProducts

-- INSTANCE (free from Core): (F

class PreservesFiniteColimits (F : C ⥤ D) : Prop where
  preservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteColimits.preservesFiniteColimits

-- INSTANCE (free from Core): (priority

lemma PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    haveI := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

attribute [local instance] uliftCategory in

lemma comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

lemma preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] :
    PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_natIso h

class PreservesFiniteCoproducts (F : C ⥤ D) : Prop where
  /-- preservation of colimits indexed by `Discrete (Fin n)`. -/
  preserves : ∀ n, PreservesColimitsOfShape (Discrete (Fin n)) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): comp_preservesFiniteCoproducts

-- INSTANCE (free from Core): (F

class ReflectsFiniteColimits (F : C ⥤ D) : Prop where
  [reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F]

attribute [instance] ReflectsFiniteColimits.reflects

lemma ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    haveI := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

class ReflectsFiniteCoproducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsColimitsOfShape (Discrete (Fin n)) F

-- INSTANCE (free from Core): (priority

lemma preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G

lemma preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesColimitsOfShape_of_reflects_of_preserves F G

-- INSTANCE (free from Core): reflectsFiniteColimitsOfReflectsIsomorphisms

-- INSTANCE (free from Core): reflectsFiniteCoproductsOfReflectsIsomorphisms

-- INSTANCE (free from Core): comp_reflectsFiniteCoproducts

-- INSTANCE (free from Core): (F

end CategoryTheory.Limits
