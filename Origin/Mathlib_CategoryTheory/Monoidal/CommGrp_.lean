/-
Extracted from CategoryTheory/Monoidal/CommGrp_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of commutative groups in a Cartesian monoidal category
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon Grp CommMon

open MonObj

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C] [BraidedCategory C]

structure CommGrp where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [grp : GrpObj X]
  [comm : IsCommMonObj X]
