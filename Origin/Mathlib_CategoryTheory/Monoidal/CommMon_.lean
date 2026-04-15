/-
Extracted from CategoryTheory/Monoidal/CommMon_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of commutative monoids in a braided monoidal category.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

variable (C) in

structure CommMon where
  /-- The underlying object in the ambient monoidal category -/
  X : C
  [mon : MonObj X]
  [comm : IsCommMonObj X]

attribute [instance] CommMon.mon CommMon.comm

namespace CommMon
