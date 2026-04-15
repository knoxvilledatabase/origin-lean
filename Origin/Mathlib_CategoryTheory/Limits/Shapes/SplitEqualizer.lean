/-
Extracted from CategoryTheory/Limits/Shapes/SplitEqualizer.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Split Equalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `ι : W ⟶ X` to be a split
equalizer: there is a retraction `r` of `ι` and a retraction `t` of `g`, which additionally satisfy
`t ≫ f = r ≫ ι`.

In addition, we show that every split equalizer is an equalizer
(`CategoryTheory.IsSplitEqualizer.isEqualizer`) and absolute
(`CategoryTheory.IsSplitEqualizer.map`)

A pair `f g : X ⟶ Y` has a split equalizer if there is a `W` and `ι : W ⟶ X` making `f,g,ι` a
split equalizer.
A pair `f g : X ⟶ Y` has a `G`-split equalizer if `G f, G g` has a split equalizer.

These definitions and constructions are useful in particular for the comonadicity theorems.

This file was adapted from `Mathlib/CategoryTheory/Limits/Shapes/SplitCoequalizer.lean`. Please try
to keep them in sync.

-/

namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {X Y : C} (f g : X ⟶ Y)

structure IsSplitEqualizer {W : C} (ι : W ⟶ X) where
  /-- A map from `X` to the equalizer -/
  leftRetraction : X ⟶ W
  /-- A map in the opposite direction to `f` and `g` -/
  rightRetraction : Y ⟶ X
  /-- Composition of `ι` with `f` and with `g` agree -/
  condition : ι ≫ f = ι ≫ g := by cat_disch
  /-- `leftRetraction` splits `ι` -/
  ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W := by cat_disch
  /-- `rightRetraction` splits `g` -/
  bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X := by cat_disch
  /-- `f` composed with `rightRetraction` is `leftRetraction` composed with `ι` -/
  top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι := by cat_disch

-- INSTANCE (free from Core): {X

open IsSplitEqualizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] ι_leftRetraction bottom_rightRetraction top_rightRetraction

variable {f g}
