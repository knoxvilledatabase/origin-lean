/-
Extracted from Algebra/Ring/CentroidHom.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Centroid homomorphisms

Let `A` be a (nonunital, non-associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`CentroidHom`) in keeping
with `AddMonoidHom` etc.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `CentroidHom`: Maps which preserve left and right multiplication.

## Typeclasses

* `CentroidHomClass`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/

assert_not_exists Field

open Function

variable {F M N R α : Type*}

structure CentroidHom (α : Type*) [NonUnitalNonAssocSemiring α] extends α →+ α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left' (a b : α) : toFun (a * b) = a * toFun b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right' (a b : α) : toFun (a * b) = toFun a * b

attribute [nolint docBlame] CentroidHom.toAddMonoidHom

class CentroidHomClass (F : Type*) (α : outParam Type*)
    [NonUnitalNonAssocSemiring α] [FunLike F α α] : Prop extends AddMonoidHomClass F α α where
  /-- Commutativity of centroid homomorphisms with left multiplication. -/
  map_mul_left (f : F) (a b : α) : f (a * b) = a * f b
  /-- Commutativity of centroid homomorphisms with right multiplication. -/
  map_mul_right (f : F) (a b : α) : f (a * b) = f a * b

export CentroidHomClass (map_mul_left map_mul_right)

-- INSTANCE (free from Core): [NonUnitalNonAssocSemiring

/-! ### Centroid homomorphisms -/

namespace CentroidHom

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
