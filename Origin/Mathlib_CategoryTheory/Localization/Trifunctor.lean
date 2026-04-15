/-
Extracted from CategoryTheory/Localization/Trifunctor.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Lifting of trifunctors

In this file, in the context of the localization of categories, we extend the notion
of lifting of functors to the case of trifunctors
(see also the file `Localization.Bifunctor` for the case of bifunctors).
The main result in this file is that we can localize "associator" isomorphisms
(see the definition `Localization.associator`).

-/

namespace CategoryTheory

open Functor

variable {C₁ C₂ C₃ C₁₂ C₂₃ D₁ D₂ D₃ D₁₂ D₂₃ C D E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
  [Category* C₁₂] [Category* C₂₃] [Category* D₁₂] [Category* D₂₃]
  [Category* C] [Category* D] [Category* E]

namespace MorphismProperty

def IsInvertedBy₃ (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    (W₃ : MorphismProperty C₃) (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) : Prop :=
  (W₁.prod (W₂.prod W₃)).IsInvertedBy (currying₃.functor.obj F)

end MorphismProperty

namespace Localization

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)

class Lifting₃ (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
    (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) where
  /-- the isomorphism `((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F` expressing
  that `F` is induced by `F'` up to an isomorphism -/
  iso (L₁ L₂ L₃ W₁ W₂ W₃ F F') : ((((whiskeringLeft₃ E).obj L₁).obj L₂).obj L₃).obj F' ≅ F

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E) [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F F']

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)

-- INSTANCE (free from Core): Lifting₃.uncurry

end

variable (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₃ : MorphismProperty C₃}
  (hF : MorphismProperty.IsInvertedBy₃ W₁ W₂ W₃ F)
  (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

noncomputable def lift₃ : D₁ ⥤ D₂ ⥤ D₃ ⥤ E :=
  curry₃.obj (lift (uncurry₃.obj F) hF (L₁.prod (L₂.prod L₃)))

-- INSTANCE (free from Core): :

end

variable (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) (L₃ : C₃ ⥤ D₃)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]
  (F₁ F₂ : C₁ ⥤ C₂ ⥤ C₃ ⥤ E) (F₁' F₂' : D₁ ⥤ D₂ ⥤ D₃ ⥤ E)
  [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₁ F₁'] [Lifting₃ L₁ L₂ L₃ W₁ W₂ W₃ F₂ F₂'] (τ : F₁ ⟶ F₂)
  (e : F₁ ≅ F₂)

noncomputable def lift₃NatTrans : F₁' ⟶ F₂' :=
  fullyFaithfulUncurry₃.preimage
    (liftNatTrans (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃)) (uncurry₃.obj F₁)
      (uncurry₃.obj F₂) (uncurry₃.obj F₁') (uncurry₃.obj F₂') (uncurry₃.map τ))

set_option backward.isDefEq.respectTransparency false in
