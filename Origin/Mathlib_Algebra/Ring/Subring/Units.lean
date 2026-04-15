/-
Extracted from Algebra/Ring/Subring/Units.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Unit subgroups of a ring

-/

def Units.posSubgroup (R : Type*) [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }
