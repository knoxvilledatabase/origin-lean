/-
Extracted from RingTheory/LocalRing/ResidueField/Ideal.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The residue field of a prime ideal

We define `Ideal.ResidueField I` to be the residue field of the local ring `Localization.Prime I`,
and provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.

-/

open scoped nonZeroDivisors

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B] (I : Ideal R) [I.IsPrime]

abbrev Ideal.ResidueField : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

noncomputable

abbrev Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R →+* S) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)
