/-
Extracted from Algebra/Star/StarRingHom.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms of star rings

This file defines a new type of morphism between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphism, namely `NonUnitalStarRingHom`, is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalRingHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalStarRingHom`

## Implementation

This file is heavily inspired by `Mathlib/Algebra/Star/StarAlgHom.lean`.

## Tags

non-unital, ring, morphism, star
-/

open EquivLike

/-! ### Non-unital star ring homomorphisms -/

structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] : Prop extends StarHomClass F A B

namespace NonUnitalStarRingHomClass

variable {F A B : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [FunLike F A B] [NonUnitalRingHomClass F A B]
