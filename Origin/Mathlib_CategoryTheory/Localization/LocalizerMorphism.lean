/-
Extracted from CategoryTheory/Localization/LocalizerMorphism.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms of localizers

A morphism of localizers consists of a functor `F : C₁ ⥤ C₂` between
two categories equipped with morphism properties `W₁` and `W₂` such
that `F` sends morphisms in `W₁` to morphisms in `W₂`.

If `Φ : LocalizerMorphism W₁ W₂`, and that `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for `W₁` and `W₂`, the induced functor `D₁ ⥤ D₂`
is denoted `Φ.localizedFunctor L₁ L₂`; we introduce the condition
`Φ.IsLocalizedEquivalence` which expresses that this functor is an equivalence
of categories. This condition is independent of the choice of the
localized categories.

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

universe v₁ v₂ v₃ v₄ v₄' v₅ v₅' v₆ u₁ u₂ u₃ u₄ u₄' u₅ u₅' u₆

namespace CategoryTheory

open Localization Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {D₁ : Type u₄} {D₂ : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} D₁] [Category.{v₅} D₂]
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)

structure LocalizerMorphism where
  /-- a functor between the two categories -/
  functor : C₁ ⥤ C₂
  /-- the functor is compatible with the `MorphismProperty` -/
  map : W₁ ≤ W₂.inverseImage functor

namespace LocalizerMorphism

variable {W₁ W₂} in
