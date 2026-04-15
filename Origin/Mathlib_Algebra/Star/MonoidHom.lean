/-
Extracted from Algebra/Star/MonoidHom.lean
Genuine: 2 of 5 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Morphisms of star monoids

This file defines the type of morphisms `StarMonoidHom` between monoids `A` and `B` where both
`A` and `B` are equipped with a `star` operation. These morphisms are star-preserving monoid
homomorphisms and are equipped with the notation `A →⋆* B`.

The primary motivation for these morphisms is to provide a target type for morphisms which induce
a corresponding morphism between the unitary groups in a star monoid.

## Main definitions

  * `StarMonoidHom`
  * `StarMulEquiv`

## Tags

monoid, star
-/

variable {F A B C D : Type*}

/-! ### Star monoid homomorphisms -/

structure StarMonoidHom (A B : Type*) [Monoid A] [Star A] [Monoid B] [Star B]
    extends A →* B where
  /-- By definition, a star monoid homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

infixr:25 " →⋆* " => StarMonoidHom

add_decl_doc StarMonoidHom.toMonoidHom

namespace StarMonoidHom

variable [Monoid A] [Star A] [Monoid B] [Star B]

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def Simps.coe (f : A →⋆* B) : A → B := f

initialize_simps_projections StarMonoidHom (toFun → coe)
