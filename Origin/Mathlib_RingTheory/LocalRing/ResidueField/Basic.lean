/-
Extracted from RingTheory/LocalRing/ResidueField/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Residue Field of local rings

We prove basic properties of the residue field of a local ring.

-/

variable {R S T : Type*}

namespace IsLocalRing

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

lemma ker_residue : RingHom.ker (residue R) = maximalIdeal R :=
  Ideal.mk_ker
