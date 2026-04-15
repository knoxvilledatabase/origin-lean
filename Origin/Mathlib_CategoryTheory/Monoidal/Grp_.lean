/-
Extracted from CategoryTheory/Monoidal/Grp_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of groups in a Cartesian monoidal category

We define group objects in Cartesian monoidal categories.

We show that the associativity diagram of a group object is always Cartesian and deduce that
morphisms of group objects commute with taking inverses.

We show that a finite-product-preserving functor takes group objects to group objects.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃ u

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory Mon MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory.{v₁} C]

class AddGrpObj (X : C) extends AddMonObj X where
  /-- The negation in a group object -/
  neg : X ⟶ X
  left_neg (X) : lift neg (𝟙 X) ≫ add = toUnit _ ≫ zero := by cat_disch
  right_neg (X) : lift (𝟙 X) neg ≫ add = toUnit _ ≫ zero := by cat_disch
