/-
Extracted from CategoryTheory/Localization/Equivalence.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localization functors are preserved through equivalences

In `Mathlib/CategoryTheory/Localization/Predicate.lean`, the lemma
`Localization.of_equivalence_target` already showed that the predicate of localized categories is
unchanged when we replace the target category (i.e. the candidate localized category) by an
equivalent category.
In this file, we show the same for the source category (`Localization.of_equivalence_source`).
More generally, `Localization.of_equivalences` shows that we may replace both the
source and target categories by equivalent categories. This is obtained using
`Localization.isEquivalence` which provide a sufficient condition in order to show
that a functor between localized categories is an equivalence.

-/

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Category* D₁] [Category* D₂]

namespace Localization

variable
  (L₁ : C₁ ⥤ D₁) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (G : C₁ ⥤ D₂) (G' : D₁ ⥤ D₂) [Lifting L₁ W₁ G G']
  (F : C₂ ⥤ D₁) (F' : D₂ ⥤ D₁) [Lifting L₂ W₂ F F']
  (α : G ⋙ F' ≅ L₁) (β : F ⋙ G' ≅ L₂)

noncomputable def equivalence : D₁ ≌ D₂ :=
  Equivalence.mk G' F' (liftNatIso L₁ W₁ L₁ (G ⋙ F') (𝟭 D₁) (G' ⋙ F') α.symm)
    (liftNatIso L₂ W₂ (F ⋙ G') L₂ (F' ⋙ G') (𝟭 D₂) β)
