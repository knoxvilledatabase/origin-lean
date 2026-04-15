/-
Extracted from CategoryTheory/Monoidal/Limits/Colimits.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tensor product of colimits

In this file, we apply the `PreservesColimit₂` API to the bifunctor
`curriedTensor C` on a monoidal category `C`.

Given cocones `c₁` and `c₂` for functors `F₁ : J₁ ⥤ C` and `F₂ : J₂ ⥤ C`,
we define a cocone `c₁.tensor₂ c₂` for the functor `J₁ × J₂ ⥤ C` obtained
using the tensor product on `C`, and we obtain that it is a colimit cocone
if both `c₁` and `c₂` are, and `PreservesColimit₂ F₁ F₂ (curriedTensor C)` holds.

We also introduce a definition `Cocone.tensor` which takes as an input two
cocones `c₁` and `c₂` for two functors `F₁ : J ⥤ C` and `F₂ : J ⥤ C` and
produces a cocone for `F₁ ⊗ F₂ : J ⥤ C` with point `c₁.pt ⊗ c₂.pt` and we show
that it is a colimit cocone when `PreservesColimit₂ F₁ F₂ (curriedTensor C)`
holds and `J` is sifted.

-/

namespace CategoryTheory.Limits

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]
  {J J₁ J₂ : Type*} [Category* J] [Category* J₁] [Category* J₂]

variable {F₁ : J₁ ⥤ C} {F₂ : J₂ ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

variable (c₁ c₂) in

abbrev Cocone.tensor₂ :
    Cocone (externalProduct F₁ F₂) :=
  (curriedTensor C).mapCocone₂ c₁ c₂

noncomputable def IsColimit.tensor₂ [PreservesColimit₂ F₁ F₂ (curriedTensor C)]
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (c₁.tensor₂ c₂) :=
  isColimitOfPreserves₂ (curriedTensor C) hc₁ hc₂

end

variable {F₁ F₂ : J ⥤ C} {c₁ : Cocone F₁} {c₂ : Cocone F₂}

variable (c₁ c₂) in
