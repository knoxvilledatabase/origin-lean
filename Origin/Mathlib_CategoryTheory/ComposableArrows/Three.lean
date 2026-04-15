/-
Extracted from CategoryTheory/ComposableArrows/Three.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# API for compositions of three arrows

Given morphisms `f₁ : i ⟶ j`, `f₂ : j ⟶ k`, `f₃ : k ⟶ l`, and their
compositions `f₁₂ : i ⟶ k` and `f₂₃ : j ⟶ l`, we define
maps `ComposableArrows.threeδ₃Toδ₂ : mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃`,
`threeδ₂Toδ₁ : mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃`, and `threeδ₁Toδ₀ : mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃`.
The names are justified by the fact that `ComposableArrow.mk₃ f₁ f₂ f₃`
can be thought of as a `3`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `3`) are respectively
`mk₂ f₂ f₃`, `mk₂ f₁₂ f₃`, `mk₂ f₁ f₂₃`, `mk₂ f₁ f₂`.

-/

universe v u

namespace CategoryTheory

namespace ComposableArrows

variable {C : Type u} [Category.{v} C]
  {i j k l : C} (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l)
  (f₁₂ : i ⟶ k) (f₂₃ : j ⟶ l)

def threeδ₃Toδ₂ (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂ ⟶ mk₂ f₁ f₂₃ :=
  homMk₂ (𝟙 _) (𝟙 _) f₃

set_option backward.isDefEq.respectTransparency false in

def threeδ₂Toδ₁ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) (h₂₃ : f₂ ≫ f₃ = f₂₃ := by cat_disch) :
    mk₂ f₁ f₂₃ ⟶ mk₂ f₁₂ f₃ :=
  homMk₂ (𝟙 _) f₂ (𝟙 _)

set_option backward.isDefEq.respectTransparency false in

def threeδ₁Toδ₀ (h₁₂ : f₁ ≫ f₂ = f₁₂ := by cat_disch) :
    mk₂ f₁₂ f₃ ⟶ mk₂ f₂ f₃ :=
  homMk₂ f₁ (𝟙 _) (𝟙 _)

variable (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)
