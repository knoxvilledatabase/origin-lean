/-
Extracted from CategoryTheory/Limits/Shapes/SplitCoequalizer.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Split coequalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `π : Y ⟶ Z` to be a split
coequalizer: there is a section `s` of `π` and a section `t` of `g`, which additionally satisfy
`t ≫ f = π ≫ s`.

In addition, we show that every split coequalizer is a coequalizer
(`CategoryTheory.IsSplitCoequalizer.isCoequalizer`) and absolute
(`CategoryTheory.IsSplitCoequalizer.map`)

A pair `f g : X ⟶ Y` has a split coequalizer if there is a `Z` and `π : Y ⟶ Z` making `f,g,π` a
split coequalizer.
A pair `f g : X ⟶ Y` has a `G`-split coequalizer if `G f, G g` has a split coequalizer.

These definitions and constructions are useful in particular for the monadicity theorems.

This file has been adapted to `Mathlib/CategoryTheory/Limits/Shapes/SplitEqualizer.lean`. Please try
to keep them in sync.

-/

namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]

variable {D : Type u₂} [Category.{v₂} D]

variable (G : C ⥤ D)

variable {X Y : C} (f g : X ⟶ Y)

structure IsSplitCoequalizer {Z : C} (π : Y ⟶ Z) where
  /-- A map from the coequalizer to `Y` -/
  rightSection : Z ⟶ Y
  /-- A map in the opposite direction to `f` and `g` -/
  leftSection : Y ⟶ X
  /-- Composition of `π` with `f` and with `g` agree -/
  condition : f ≫ π = g ≫ π := by cat_disch
  /-- `rightSection` splits `π` -/
  rightSection_π : rightSection ≫ π = 𝟙 Z := by cat_disch
  /-- `leftSection` splits `g` -/
  leftSection_bottom : leftSection ≫ g = 𝟙 Y := by cat_disch
  /-- `leftSection` composed with `f` is `pi` composed with `rightSection` -/
  leftSection_top : leftSection ≫ f = π ≫ rightSection := by cat_disch

-- INSTANCE (free from Core): {X

open IsSplitCoequalizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] rightSection_π leftSection_bottom leftSection_top

variable {f g}
