/-
Extracted from Algebra/Lie/NonUnitalNonAssocAlgebra.lean
Genuine: 1 of 8 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Lie algebras as non-unital, non-associative algebras

The definition of Lie algebras uses the `Bracket` typeclass for multiplication whereas we have a
separate `Mul` typeclass used for general algebras.

It is useful to have a special typeclass for Lie algebras because:
* it enables us to use the traditional notation `⁅x, y⁆` for the Lie multiplication,
* associative algebras carry a natural Lie algebra structure via the ring commutator and so we
  need them to carry both `Mul` and `Bracket` simultaneously,
* more generally, Poisson algebras (not yet defined) need both typeclasses.

However there are times when it is convenient to be able to regard a Lie algebra as a general
algebra and we provide some basic definitions for doing so here.

## Main definitions

  * `CommutatorRing` turns a Lie ring into a `NonUnitalNonAssocRing` by turning its
    `Bracket` (denoted `⁅ , ⁆`) into a `Mul` (denoted `*`).
  * `LieHom.toNonUnitalAlgHom`

## Tags

lie algebra, non-unital, non-associative
-/

universe u v w

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

def CommutatorRing (L : Type v) : Type v := L

-- INSTANCE (free from Core): :

namespace LieAlgebra

-- INSTANCE (free from Core): (L

-- INSTANCE (free from Core): (L

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): isScalarTower

-- INSTANCE (free from Core): smulCommClass

end LieAlgebra

namespace LieHom

variable {R L}

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]
