/-
Extracted from CategoryTheory/Limits/FunctorCategory/Shapes/Products.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Co)products in functor categories

Given `f : α → D ⥤ C`, we prove the isomorphisms
`(∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d)` and `(∐ f).obj d ≅ ∐ (fun s => (f s).obj d)`.

-/

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
  {α : Type w}

section Product

variable [HasLimitsOfShape (Discrete α) C]

noncomputable def piObjIso (f : α → D ⥤ C) (d : D) : (∏ᶜ f).obj d ≅ ∏ᶜ (fun s => (f s).obj d) :=
  limitObjIsoLimitCompEvaluation (Discrete.functor f) d ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

set_option backward.isDefEq.respectTransparency false in
