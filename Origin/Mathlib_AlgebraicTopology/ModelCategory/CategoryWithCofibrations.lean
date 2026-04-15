/-
Extracted from AlgebraicTopology/ModelCategory/CategoryWithCofibrations.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Categories with classes of fibrations, cofibrations, weak equivalences

We introduce typeclasses `CategoryWithFibrations`, `CategoryWithCofibrations` and
`CategoryWithWeakEquivalences` to express that a category `C` is equipped with
classes of morphisms named "fibrations", "cofibrations" or "weak equivalences".

-/

universe v u

namespace HomotopicalAlgebra

open CategoryTheory

variable (C : Type u) [Category.{v} C]

class CategoryWithFibrations where
  /-- the class of fibrations -/
  fibrations : MorphismProperty C

class CategoryWithCofibrations where
  /-- the class of cofibrations -/
  cofibrations : MorphismProperty C

class CategoryWithWeakEquivalences where
  /-- the class of weak equivalences -/
  weakEquivalences : MorphismProperty C

variable {X Y : C} (f : X ⟶ Y)

section Fib

variable [CategoryWithFibrations C]

def fibrations : MorphismProperty C := CategoryWithFibrations.fibrations

variable {C}
