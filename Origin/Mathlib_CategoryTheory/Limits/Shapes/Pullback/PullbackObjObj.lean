/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/PullbackObjObj.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Leibniz Constructions

Let `F : C₁ ⥤ C₂ ⥤ C₃`. Given morphisms `f₁ : X₁ ⟶ Y₁` in `C₁`
and `f₂ : X₂ ⟶ Y₂` in `C₂`, we introduce a structure
`F.PushoutObjObj f₁ f₂` which contains the data of a
pushout of `(F.obj Y₁).obj X₂` and `(F.obj X₁).obj Y₂`
along `(F.obj X₁).obj X₂`. If `sq₁₂ : F.PushoutObjObj f₁ f₂`,
we have a canonical "inclusion" `sq₁₂.ι : sq₁₂.pt ⟶ (F.obj Y₁).obj Y₂`.

If `C₃` has pushouts, then we define the Leibniz pushout (often called pushout-product) as the
canonical inclusion `(PushoutObjObj.ofHasPushout F f₁ f₂).ι`. This defines a bifunctor
`F.leibnizPushout : Arrow C₁ ⥤ Arrow C₂ ⥤ Arrow C₃`.

Similarly, if we have a bifunctor `G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂`, and
morphisms `f₁ : X₁ ⟶ Y₁` in `C₁` and `f₃ : X₃ ⟶ Y₃` in `C₃`,
we introduce a structure `F.PullbackObjObj f₁ f₃` which
contains the data of a pullback of `(G.obj (op X₁)).obj X₃`
and `(G.obj (op Y₁)).obj Y₃` over `(G.obj (op X₁)).obj Y₃`.
If `sq₁₃ : F.PullbackObjObj f₁ f₃`, we have a canonical
projection `sq₁₃.π : (G.obj Y₁).obj X₃ ⟶ sq₁₃.pt`.

If `C₂` has pullbacks, then we define the Leibniz pullback (often called pullback-hom) as the
canonical projection `(PullbackObjObj.ofHasPullback G f₁ f₃).π`. This defines a bifunctor
`G.leibnizPullback : (Arrow C₁)ᵒᵖ ⥤ Arrow C₃ ⥤ Arrow C₂`.

If `C₂` has pullbacks and `C₃` has pushouts, then a parameterized adjunction `adj₂ : F ⊣₂ G` induces
a parameterized adjunction `F.leibnizAdjunction G adj₂ : F.leibnizPushout ⊣₂ G.leibnizPullback`.

## References

* [Emily Riehl, Dominic Verity, *Elements of ∞-Category Theory*, Definition C.2.8][RV22]
* https://ncatlab.org/nlab/show/pushout-product
* https://ncatlab.org/nlab/show/pullback-power

## Tags

pushout-product, pullback-hom, pullback-power, Leibniz
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace Functor

variable {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) {X₂ Y₂ : C₂} (f₂ : X₂ ⟶ Y₂)

structure PushoutObjObj where
  /-- the pushout -/
  pt : C₃
  /-- the first inclusion -/
  inl : (F.obj Y₁).obj X₂ ⟶ pt
  /-- the second inclusion -/
  inr : (F.obj X₁).obj Y₂ ⟶ pt
  isPushout : IsPushout ((F.map f₁).app X₂) ((F.obj X₁).map f₂) inl inr

namespace PushoutObjObj
