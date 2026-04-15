/-
Extracted from Algebra/Category/MonCat/Colimits.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The category of monoids has all colimits.

We do this construction knowing nothing about monoids.
In particular, I want to claim that this file could be produced by a python script
that just looks at what Lean 3's `#print monoid` printed a long time ago (it no longer looks like
this due to the addition of `npow` fields):
```
structure monoid : Type u → Type u
fields:
monoid.mul : Π {M : Type u} [self : monoid M], M → M → M
monoid.mul_assoc : ∀ {M : Type u} [self : monoid M] (a b c : M), a * b * c = a * (b * c)
monoid.one : Π {M : Type u} [self : monoid M], M
monoid.one_mul : ∀ {M : Type u} [self : monoid M] (a : M), 1 * a = a
monoid.mul_one : ∀ {M : Type u} [self : monoid M] (a : M), a * 1 = a
```

and if we'd fed it the output of Lean 3's `#print comm_ring`, this file would instead build
colimits of commutative rings.

A slightly bolder claim is that we could do this with tactics, as well.

Note: `Monoid` and `CommRing` are no longer flat structures in Mathlib4, and so `#print Monoid`
gives the less clear
```
inductive Monoid.{u} : Type u → Type u
number of parameters: 1
constructors:
Monoid.mk : {M : Type u} →
  [toSemigroup : Semigroup M] →
    [toOne : One M] →
      (∀ (a : M), 1 * a = a) →
        (∀ (a : M), a * 1 = a) →
          (npow : ℕ → M → M) →
            autoParam (∀ (x : M), npow 0 x = 1) _auto✝ →
              autoParam (∀ (n : ℕ) (x : M), npow (n + 1) x = x * npow n x) _auto✝¹ → Monoid M
```
-/

assert_not_exists MonoidWithZero

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace MonCat.Colimits

/-!
We build the colimit of a diagram in `MonCat` by constructing the
free monoid on the disjoint union of all the monoids in the diagram,
then taking the quotient by the monoid laws within each monoid,
and the identifications given by the morphisms in the diagram.
-/

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

inductive Prequotient
  -- There's always `of`
  | of : ∀ (j : J) (_ : F.obj j), Prequotient
  -- Then one generator for each operation
  | one : Prequotient
  | mul : Prequotient → Prequotient → Prequotient

-- INSTANCE (free from Core): :

open Prequotient

inductive Relation : Prequotient F → Prequotient F → Prop -- Make it an equivalence relation:
  | refl : ∀ x, Relation x x
  | symm : ∀ (x y) (_ : Relation x y), Relation y x
  | trans : ∀ (x y z) (_ : Relation x y) (_ : Relation y z),
      Relation x z -- There's always a `map` relation
  | map :
    ∀ (j j' : J) (f : j ⟶ j') (x : F.obj j),
      -- Then one relation per operation, describing the interaction with `of`
      Relation (Prequotient.of j' ((F.map f) x)) (Prequotient.of j x)
  | mul : ∀ (j) (x y : F.obj j), Relation (Prequotient.of j (x * y))
      (mul (Prequotient.of j x) (Prequotient.of j y))
  | one : ∀ j, Relation (Prequotient.of j 1) one -- Then one relation per argument of each operation
  | mul_1 : ∀ (x x' y) (_ : Relation x x'), Relation (mul x y) (mul x' y)
  | mul_2 : ∀ (x y y') (_ : Relation y y'), Relation (mul x y) (mul x y')
    -- And one relation per axiom
  | mul_assoc : ∀ x y z, Relation (mul (mul x y) z) (mul x (mul y z))
  | one_mul : ∀ x, Relation (mul one x) x
  | mul_one : ∀ x, Relation (mul x one) x

-- INSTANCE (free from Core): colimitSetoid

def ColimitType : Type v :=
  Quotient (colimitSetoid F)

deriving Inhabited

-- INSTANCE (free from Core): monoidColimitType
