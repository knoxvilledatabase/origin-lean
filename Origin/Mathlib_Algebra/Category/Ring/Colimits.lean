/-
Extracted from Algebra/Category/Ring/Colimits.lean
Genuine: 3 of 12 | Dissolved: 0 | Infrastructure: 9
-/
import Origin.Core

/-!
# The category of commutative rings has all colimits.

This file uses a "pre-automated" approach, just as for
`Mathlib/Algebra/Category/MonCat/Colimits.lean`.
It is a very uniform approach, that conceivably could be synthesised directly
by a tactic that analyses the shape of `CommRing` and `RingHom`.
-/

universe u v

open CategoryTheory Limits

namespace RingCat.Colimits

/-!
We build the colimit of a diagram in `RingCat` by constructing the
free ring on the disjoint union of all the rings in the diagram,
then taking the quotient by the ring laws within each ring,
and the identifications given by the morphisms in the diagram.
-/

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | zero : Prequotient
  | one : Prequotient
  | neg : Prequotient → Prequotient
  | add : Prequotient → Prequotient → Prequotient
  | mul : Prequotient → Prequotient → Prequotient

-- INSTANCE (free from Core): :

open Prequotient

inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence Relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z), Relation x z
  -- There's always a `map` Relation
  | map : ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      Relation (Prequotient.of j' (F.map f x))
        (Prequotient.of j x)
  -- Then one Relation per operation, describing the interaction with `of`
  | zero : ∀ j, Relation (Prequotient.of j 0) zero
  | one : ∀ j, Relation (Prequotient.of j 1) one
  | neg : ∀ (j) (x : F.obj j), Relation (Prequotient.of j (-x)) (neg (Prequotient.of j x))
  | add : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x + y))
      (add (Prequotient.of j x) (Prequotient.of j y))
  | mul : ∀ (j) (x y : F.obj j),
      Relation (Prequotient.of j (x * y))
        (mul (Prequotient.of j x) (Prequotient.of j y))
  -- Then one Relation per argument of each operation
  | neg_1 : ∀ (x x') (_ : Relation x x'), Relation (neg x) (neg x')
  | add_1 : ∀ (x x' y) (_ : Relation x x'), Relation (add x y) (add x' y)
  | add_2 : ∀ (x y y') (_ : Relation y y'), Relation (add x y) (add x y')
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
  -- And one Relation per axiom
  | zero_add : ∀ x, Relation (add zero x) x
  | add_zero : ∀ x, Relation (add x zero) x
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x
  | neg_add_cancel : ∀ x, Relation (add (neg x) x) zero
  | add_comm : ∀ x y, Relation (add x y) (add y x)
  | add_assoc : ∀ x y z, Relation (add (add x y) z) (add x (add y z))
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | left_distrib : ∀ x y z, Relation (mul x (add y z)) (add (mul x y) (mul x z))
  | right_distrib : ∀ x y z, Relation (mul (add x y) z) (add (mul x z) (mul y z))
  | zero_mul : ∀ x, Relation (mul zero x) zero
  | mul_zero : ∀ x, Relation (mul x zero) zero

-- INSTANCE (free from Core): colimitSetoid

def ColimitType : Type v :=
  Quotient (colimitSetoid F)

-- INSTANCE (free from Core): ColimitType.instZero

-- INSTANCE (free from Core): ColimitType.instAdd

-- INSTANCE (free from Core): ColimitType.instNeg

-- INSTANCE (free from Core): ColimitType.AddGroup

-- INSTANCE (free from Core): InhabitedColimitType

-- INSTANCE (free from Core): ColimitType.AddGroupWithOne

-- INSTANCE (free from Core): :
