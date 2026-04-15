/-
Extracted from Algebra/Star/StarAlgHom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Morphisms of star algebras

This file defines morphisms between `R`-algebras (unital or non-unital) `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms, namely `StarAlgHom` and
`NonUnitalStarAlgHom` are direct extensions of their non-`star`red counterparts with a field
`map_star` which guarantees they preserve the star operation. We keep the type classes as generic
as possible, in keeping with the definition of `NonUnitalAlgHom` in the non-unital case. In this
file, we only assume `Star` unless we want to talk about the zero map as a
`NonUnitalStarAlgHom`, in which case we need `StarAddMonoid`. Note that the scalar ring `R`
is not required to have a star operation, nor do we need `StarRing` or `StarModule` structures on
`A` and `B`.

As with `NonUnitalAlgHom`, in the non-unital case the multiplications are not assumed to be
associative or unital, or even to be compatible with the scalar actions. In a typical application,
the operations will satisfy compatibility conditions making them into algebras (albeit possibly
non-associative and/or non-unital) but such conditions are not required here for the definitions.

The primary impetus for defining these types is that they constitute the morphisms in the categories
of unital C⋆-algebras (with `StarAlgHom`s) and of C⋆-algebras (with `NonUnitalStarAlgHom`s).

## Main definitions

  * `NonUnitalStarAlgHom`
  * `StarAlgHom`

## Tags

non-unital, algebra, morphism, star
-/

open EquivLike

/-! ### Non-unital star algebra homomorphisms -/

structure NonUnitalStarAlgHom (R A B : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A] [Star A] [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
  [Star B] extends A →ₙₐ[R] B where
  /-- By definition, a non-unital ⋆-algebra homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)
