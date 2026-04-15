/-
Extracted from CategoryTheory/ObjectProperty/Shift.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Properties of objects on categories equipped with shift

Given a predicate `P : ObjectProperty C` on objects of a category equipped with a shift
by `A`, we define shifted properties of objects `P.shift a` for all `a : A`.
We also introduce a typeclass `P.IsStableUnderShift A` to say that `P X`
implies `P (X⟦a⟧)` for all `a : A`.

-/

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]
  {E : Type*} [Category* E] [HasShift E A]

namespace ObjectProperty

def shift (a : A) : ObjectProperty C := fun X => P (X⟦a⟧)

-- INSTANCE (free from Core): (a

variable (A)
