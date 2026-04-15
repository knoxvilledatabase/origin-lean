/-
Extracted from CategoryTheory/Localization/Bifunctor.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lifting of bifunctors

In this file, in the context of the localization of categories, we extend the notion
of lifting of functors to the case of bifunctors. As the localization of categories
behaves well with respect to finite products of categories (when the classes of
morphisms contain identities), all the definitions for bifunctors `C₁ ⥤ C₂ ⥤ E`
are obtained by reducing to the case of functors `(C₁ × C₂) ⥤ E` by using
currying and uncurrying.

Given morphism properties `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂`,
and a functor `F : C₁ ⥤ C₂ ⥤ E`, we define `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`
as the condition that the functor `uncurry.obj F : C₁ × C₂ ⥤ E` inverts `W₁.prod W₂`.

If `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are localization functors for `W₁` and `W₂`
respectively, and `F : C₁ ⥤ C₂ ⥤ E` satisfies `MorphismProperty.IsInvertedBy₂ W₁ W₂ F`,
we introduce `Localization.lift₂ F hF L₁ L₂ : D₁ ⥤ D₂ ⥤ E` which is a bifunctor
which lifts `F`.

-/

namespace CategoryTheory

open Category Functor

variable {C₁ C₂ D₁ D₂ E E' : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* E] [Category* E']

namespace MorphismProperty

def IsInvertedBy₂ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) : Prop :=
  (W₁.prod W₂).IsInvertedBy (uncurry.obj F)

end MorphismProperty

namespace Localization

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

class Lifting₂ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) where
  /-- the isomorphism `(((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F` expressing
  that `F` is induced by `F'` up to an isomorphism -/
  iso (L₁ L₂ W₁ W₂ F F') : (((whiskeringLeft₂ E).obj L₁).obj L₂).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  (F : C₁ ⥤ C₂ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ E) [Lifting₂ L₁ L₂ W₁ W₂ F F']
