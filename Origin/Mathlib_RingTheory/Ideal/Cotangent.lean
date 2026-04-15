/-
Extracted from RingTheory/Ideal/Cotangent.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `Ideal.cotangentEquivIdeal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

namespace Ideal

universe u v w

variable {R : Type u} {S : Type v} {S' : Type w} [CommRing R] [CommSemiring S] [Algebra S R]

variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)

deriving Inhabited, AddCommGroup, Module (R ⧸ I)

-- INSTANCE (free from Core): Module

variable [IsNoetherian R I] in

-- INSTANCE (free from Core): IsNoetherian
