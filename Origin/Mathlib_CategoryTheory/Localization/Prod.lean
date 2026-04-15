/-
Extracted from CategoryTheory/Localization/Prod.lean
Genuine: 8 of 9 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localization of product categories

In this file, it is shown that if functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for morphisms properties `W₁` and `W₂`, then
the product functor `C₁ × C₂ ⥤ D₁ × D₂` is a localization functor for
`W₁.prod W₂ : MorphismProperty (C₁ × C₂)`, at least if both `W₁` and `W₂`
contain identities. This main result is the instance `Functor.IsLocalization.prod`.

The proof proceeds by showing first `Localization.Construction.prodIsLocalization`,
which asserts that this holds for the localization functors `W₁.Q` and `W₂.Q` to
the constructed localized categories: this is done by showing that the product
functor `W₁.Q.prod W₂.Q : C₁ × C₂ ⥤ W₁.Localization × W₂.Localization` satisfies
the strict universal property of the localization for `W₁.prod W₂`. The general
case follows by transporting this result through equivalences of categories.

-/

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  (L₁ : C₁ ⥤ D₁) {W₁ : MorphismProperty C₁}
  (L₂ : C₂ ⥤ D₂) {W₂ : MorphismProperty C₂}

namespace Localization

namespace StrictUniversalPropertyFixedTarget

variable {E : Type u₅} [Category.{v₅} E] (F : C₁ × C₂ ⥤ E)

lemma prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
    (h : (W₁.Q.prod W₂.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) :
      F₁ = F₂ := by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

noncomputable def prodLift₁ [W₂.ContainsIdentities]
    (hF : (W₁.prod W₂).IsInvertedBy F) :
    W₁.Localization ⥤ C₂ ⥤ E :=
  Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
    haveI : ∀ (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
      fun X₂ => hF _ ⟨hf₁, MorphismProperty.id_mem _ _⟩
    apply NatIso.isIso_of_isIso_app)

variable (hF : (W₁.prod W₂).IsInvertedBy F)

lemma prod_fac₁ [W₂.ContainsIdentities] :
    W₁.Q ⋙ prodLift₁ F hF = curry.obj F :=
  Construction.fac _ _

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

noncomputable def prodLift :
    W₁.Localization × W₂.Localization ⥤ E := by
  refine uncurry.obj (Construction.lift (prodLift₁ F hF).flip ?_).flip
  intro _ _ f₂ hf₂
  haveI : ∀ (X₁ : W₁.Localization),
      IsIso (((Functor.flip (prodLift₁ F hF)).map f₂).app X₁) := fun X₁ => by
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact ((MorphismProperty.isomorphisms E).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
          (hF _ ⟨MorphismProperty.id_mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app

lemma prod_fac₂ :
    W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip := by
  simp only [prodLift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac

lemma prod_fac :
    (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F := by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip', prod_fac₂, Functor.flip_flip, prod_fac₁,
    Functor.uncurry_obj_curry_obj]

variable (W₁ W₂)

noncomputable def prod :
    StrictUniversalPropertyFixedTarget (W₁.Q.prod W₂.Q) (W₁.prod W₂) E where
  inverts := (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := fun F hF => prodLift F hF
  fac := fun F hF => prod_fac F hF
  uniq := prod_uniq

end StrictUniversalPropertyFixedTarget

variable (W₁ W₂)

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

lemma Construction.prodIsLocalization :
    (W₁.Q.prod W₂.Q).IsLocalization (W₁.prod W₂) :=
  Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (W₁ W₂)

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

-- INSTANCE (free from Core): prod

end IsLocalization

end Functor

end CategoryTheory
