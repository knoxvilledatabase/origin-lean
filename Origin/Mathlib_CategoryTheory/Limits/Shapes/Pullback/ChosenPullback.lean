/-
Extracted from CategoryTheory/Limits/Shapes/Pullback/ChosenPullback.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Chosen pullbacks

Given two morphisms `f₁ : X₁ ⟶ S` and `f₂ : X₂ ⟶ S`, we introduce
a structure `ChosenPullback f₁ f₂` which contains the data of
pullback of `f₁` and `f₂`.

## TODO
* relate this to `ChosenPullbacksAlong` which is defined in
`LocallyCartesianClosed.ChosenPullbacksAlong`.

-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

structure ChosenPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) where
  /-- the pullback -/
  pullback : C
  /-- the first projection -/
  p₁ : pullback ⟶ X₁
  /-- the second projection -/
  p₂ : pullback ⟶ X₂
  condition : p₁ ≫ f₁ = p₂ ≫ f₂
  /-- `pullback` is a pullback of `f₁` and `f₂` -/
  isLimit : IsLimit (PullbackCone.mk _ _ condition)
  /-- the projection `pullback ⟶ S` -/
  p : pullback ⟶ S := p₁ ≫ f₁
  hp₁ : p₁ ≫ f₁ = p := by cat_disch

namespace ChosenPullback

variable {X₁ X₂ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
  (h : ChosenPullback f₁ f₂)

attribute [reassoc] condition

attribute [reassoc (attr := simp, grind =)] hp₁
