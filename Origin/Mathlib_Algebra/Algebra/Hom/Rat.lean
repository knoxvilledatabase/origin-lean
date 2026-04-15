/-
Extracted from Algebra/Algebra/Hom/Rat.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homomorphisms of `ℚ`-algebras

-/

namespace RingHom

variable {R S : Type*}

def toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }
