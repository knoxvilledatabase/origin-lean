/-
Extracted from CategoryTheory/Sites/Descent/DescentDataPrime.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Descent data when we have pullbacks

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
a family of maps `f i : X i ⟶ S` in the category `C`, chosen pullbacks `sq`
and threefold wide pullbacks `sq₃` for these morphisms, we define a
category `F.DescentData' sq sq₃` of objects over the `X i`
equipped with a descent data relative to the morphisms `f i : X i ⟶ S`, where
the data and compatibilities are expressed using the chosen pullbacks.

-/

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

namespace DescentData'

variable {F sq}

variable {obj obj' : ∀ (i : ι), F.obj (.mk (op (X i)))}
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj' j))

noncomputable def pullHom' ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj' i₂) :=
  pullHom (hom i₁ i₂) ((sq i₁ i₂).isPullback.lift f₁ f₂ (by cat_disch)) f₁ f₂
