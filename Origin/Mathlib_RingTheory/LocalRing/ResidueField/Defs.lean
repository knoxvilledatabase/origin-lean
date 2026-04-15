/-
Extracted from RingTheory/LocalRing/ResidueField/Defs.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Residue Field of local rings

## Main definitions

* `IsLocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.
* `IsLocalRing.residue`: The quotient map from a local ring to its residue field.
-/

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def ResidueField :=
  R ⧸ maximalIdeal R

deriving CommRing, Inhabited

-- INSTANCE (free from Core): ResidueField.field

def residue : R →+* ResidueField R :=
  Ideal.Quotient.mk _

end IsLocalRing
