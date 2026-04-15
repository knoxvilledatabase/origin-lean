/-
Extracted from CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of pointwise right derived functors via derivability structures

In this file, we show how a right derivability structure can be used in
order to construct (pointwise) right derived functors.
Let `Φ` be a right derivability structure from `W₁ : MorphismProperty C₁`
to `W₂ : MorphismProperty C₂`. Let `F : C₂ ⥤ H` be a functor.
Then, the lemma `hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure`
says that `F` has a pointwise right derived functor with respect to `W₂`
if and only if `Φ.functor ⋙ F` has a pointwise right derived functor
with respect to `W₁`. This is essentially the Proposition 5.5 from the article
*Structures de dérivabilité* by Bruno Kahn and Georges Maltsiniotis (there,
it was stated in terms of absolute derived functors).

In particular, if `Φ.functor ⋙ F` inverts `W₁`, it follows that the
right derived functor of `F` with respect to `W₂` exists.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Limits Category Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₄} D₁] [Category.{v₅} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  (F : C₂ ⥤ H) (F₁ : D₁ ⥤ H) (α₁ : Φ.functor ⋙ F ⟶ L₁ ⋙ F₁)
  (F₂ : D₂ ⥤ H) (α₂ : F ⟶ L₂ ⋙ F₂)
  [F₁.IsRightDerivedFunctor α₁ W₁]

noncomputable def rightDerivedFunctorComparison :
    F₁ ⟶ Φ.localizedFunctor L₁ L₂ ⋙ F₂ :=
  F₁.rightDerivedDesc α₁ W₁ (Φ.localizedFunctor L₁ L₂ ⋙ F₂)
    (whiskerLeft _ α₂ ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight ((Φ.catCommSq L₁ L₂).iso).hom F₂ ≫ (Functor.associator _ _ _).hom)
