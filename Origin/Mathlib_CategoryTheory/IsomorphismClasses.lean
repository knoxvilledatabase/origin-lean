/-
Extracted from CategoryTheory/IsomorphismClasses.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Objects of a category up to an isomorphism

`IsIsomorphic X Y := Nonempty (X ≅ Y)` is an equivalence relation on the objects of a category.
The quotient with respect to this relation defines a functor from our category to `Type`.
-/

universe v u

namespace CategoryTheory

section Category

variable {C : Type u} [Category.{v} C]

def IsIsomorphic : C → C → Prop := fun X Y => Nonempty (X ≅ Y)

variable (C)
