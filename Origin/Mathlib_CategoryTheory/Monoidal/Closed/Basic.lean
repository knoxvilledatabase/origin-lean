/-
Extracted from CategoryTheory/Monoidal/Closed/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Closed monoidal categories

Define (right) closed objects and (right) closed monoidal categories.

## TODO
Some theorems about Cartesian closed categories
should be generalised and moved to this file.
-/

universe v u u₂ v₂

namespace CategoryTheory

open Category MonoidalCategory

class Closed {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (X : C) where
  /-- a choice of a right adjoint for `tensorLeft X` -/
  rightAdj : C ⥤ C
  /-- `tensorLeft X` is a left adjoint -/
  adj : tensorLeft X ⊣ rightAdj

class MonoidalClosed (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  closed (X : C) : Closed X := by infer_instance

-- INSTANCE (free from Core): 100]

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
