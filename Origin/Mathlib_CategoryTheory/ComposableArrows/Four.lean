/-
Extracted from CategoryTheory/ComposableArrows/Four.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# API for compositions of four arrows

Given morphisms `f₁ : i₀ ⟶ i₁`, `f₂ : i₁ ⟶ i₂`, `f₃ : i₂ ⟶ i₃`, `f₄ : i₃ ⟶ i₄`,
and their compositions `f₁₂ : i₀ ⟶ i₂`, `f₂₃ : i₁ ⟶ i₃` and `f₃₄ : i₂ ⟶ i₄`,
we define maps `ComposableArrows.fourδ₄Toδ₃ : mk₃ f₁ f₂ f₃ ⟶ mk₂ f₁ f₂ f₃₄`,
`fourδ₃Toδ₂ : mk₃ f₁ f₂ f₃₄ ⟶ mk₂ f₁ f₂₃ f₄`,
`fourδ₂Toδ₁ : mk₃ f₁ f₂₃ f₄ ⟶ mk₂ f₁₂ f₃ f₄`, and
`fourδ₁Toδ₀ : mk₃ f₁₂ f₃ f₄ ⟶ mk₂ f₂ f₃ f₄`.
The names are justified by the fact that `ComposableArrow.mk₄ f₁ f₂ f₃ f₄`
can be thought of as a `4`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `4`) are respectively
`mk₂ f₂ f₃ f₄`, `mk₂ f₁₂ f₃ f₄`, `mk₂ f₁ f₂₃ f₄`, `mk₂ f₁ f₂ f₃₄` and
`mk₂ f₁ f₂ f₃`.

-/

namespace CategoryTheory

namespace ComposableArrows

variable {C : Type*} [Category* C]
  {i₀ i₁ i₂ i₃ i₄ : C} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₄ : i₃ ⟶ i₄)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃) (f₃₄ : i₂ ⟶ i₄)

set_option backward.isDefEq.respectTransparency false in

def fourδ₄Toδ₃ (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch) :
    mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃₄ :=
  homMk₃ (𝟙 _) (𝟙 _) (𝟙 _) f₄

set_option backward.isDefEq.respectTransparency false in

def fourδ₃Toδ₂ (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) (h₃₄ : f₃ ≫ f₄ = f₃₄ := by cat_disch) :
    mk₃ f₁ f₂ f₃₄ ⟶ mk₃ f₁ f₂₃ f₄ :=
  homMk₃ (𝟙 _) (𝟙 _) f₃ (𝟙 _)

set_option backward.isDefEq.respectTransparency false in

def fourδ₂Toδ₁ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₃ f₁ f₂₃ f₄ ⟶ mk₃ f₁₂ f₃ f₄ :=
  homMk₃ (𝟙 _) f₂ (𝟙 _) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in

def fourδ₁Toδ₀ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) :
    mk₃ f₁₂ f₃ f₄ ⟶ mk₃ f₂ f₃ f₄ :=
  homMk₃ f₁ (𝟙 _) (𝟙 _) (𝟙 _)

variable (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃) (h₃₄ : f₃ ≫ f₄ = f₃₄)
