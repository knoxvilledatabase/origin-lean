/-
Extracted from CategoryTheory/ComposableArrows/Two.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# API for compositions of two arrows

Given morphisms `f : i ⟶ j`, `g : j ⟶ k`, and `fg : i ⟶ k` in a category `C`
such that `f ≫ g = fg`, we define maps `twoδ₂Toδ₁ : mk₁ f ⟶ mk₁ fg` and
`twoδ₁Toδ₀ : mk₁ fg ⟶ mk₁ g` in the category `ComposableArrows C 1`.
The names are justified by the fact that `ComposableArrow.mk₂ f g`
can be thought of as a `2`-simplex in the simplicial set `nerve C`,
and its faces (numbered from `0` to `2`) are respectively `mk₁ g`,
`mk₁ fg` and `mk₁ f`.

-/

namespace CategoryTheory

namespace ComposableArrows

variable {C : Type*} [Category* C]
  {i j k : C} (f : i ⟶ j) (g : j ⟶ k) (fg : i ⟶ k)

def twoδ₂Toδ₁ (h : f ≫ g = fg := by cat_disch) :
    mk₁ f ⟶ mk₁ fg :=
  homMk₁ (𝟙 _) g

def twoδ₁Toδ₀ (h : f ≫ g = fg := by cat_disch) :
    mk₁ fg ⟶ mk₁ g :=
  homMk₁ f (𝟙 _)

variable (h : f ≫ g = fg)
