/-
Extracted from CategoryTheory/Retract.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Retracts

Defines retracts of objects and morphisms.

-/

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

structure Retract (X Y : C) where
  /-- the split monomorphism -/
  i : X ⟶ Y
  /-- the split epimorphism -/
  r : Y ⟶ X
  retract : i ≫ r = 𝟙 X := by cat_disch

namespace Retract

attribute [reassoc (attr := simp)] retract

variable {X Y : C} (h : Retract X Y)

open Opposite
