/-
Extracted from Algebra/Ring/Aut.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Ring automorphisms

This file defines the automorphism group structure on `RingAut R := RingEquiv R R`.

## Implementation notes

The definition of multiplication in the automorphism group agrees with function composition,
multiplication in `Equiv.Perm`, and multiplication in `CategoryTheory.End`, but not with
`CategoryTheory.comp`.

## Tags

ring aut
-/

variable (R : Type*) [Mul R] [Add R]

abbrev RingAut := RingEquiv R R

namespace RingAut

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

def toAddAut : RingAut R →* AddAut R where
  toFun := RingEquiv.toAddEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

def toMulAut : RingAut R →* MulAut R where
  toFun := RingEquiv.toMulEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

def toPerm : RingAut R →* Equiv.Perm R where
  toFun := RingEquiv.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

variable {R}
