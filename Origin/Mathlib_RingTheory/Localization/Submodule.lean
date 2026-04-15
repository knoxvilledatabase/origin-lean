/-
Extracted from RingTheory/Localization/Submodule.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S]

namespace IsLocalization

def coeSubmodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I

theorem coeSubmodule_mono {I J : Ideal R} (h : I ≤ J) : coeSubmodule S I ≤ coeSubmodule S J :=
  Submodule.map_mono h
