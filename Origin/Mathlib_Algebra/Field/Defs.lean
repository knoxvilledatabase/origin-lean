/-
Extracted from Algebra/Field/Defs.lean
Genuine: 2 of 6 | Dissolved: 3 | Infrastructure: 1
-/
import Origin.Core

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `FieldTheory` folder.

## Main definitions

* `DivisionSemiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `DivisionRing`: Nontrivial ring with multiplicative inverses for nonzero elements.
* `Semifield`: Commutative division semiring.
* `Field`: Commutative division ring.
* `IsField`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `GroupWithZero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `GroupWithZero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

assert_not_imported Mathlib.Tactic.Common

assert_not_imported Mathlib.Algebra.NeZero

assert_not_exists MonoidHom Set

open Function

universe u

variable {K : Type*}

def NNRat.castRec [NatCast K] [Div K] (q : ℚ≥0) : K := q.num / q.den

def Rat.castRec [NatCast K] [IntCast K] [Div K] (q : ℚ) : K := q.num / q.den

-- DISSOLVED: DivisionSemiring

-- DISSOLVED: DivisionRing

-- INSTANCE (free from Core): (priority

-- DISSOLVED: Semifield
