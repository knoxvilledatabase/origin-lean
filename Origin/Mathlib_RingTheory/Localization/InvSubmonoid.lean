/-
Extracted from RingTheory/Localization/InvSubmonoid.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Submonoid of inverses

## Main definitions

* `IsLocalization.invSubmonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
  each element `x ∈ M`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]

variable [Algebra R S]

open Function

namespace IsLocalization

section InvSubmonoid

def invSubmonoid : Submonoid S :=
  (M.map (algebraMap R S)).leftInv

variable [IsLocalization M S]

theorem submonoid_map_le_is_unit : M.map (algebraMap R S) ≤ IsUnit.submonoid S := by
  rintro _ ⟨a, ha, rfl⟩
  exact IsLocalization.map_units S ⟨_, ha⟩

noncomputable abbrev equivInvSubmonoid : M.map (algebraMap R S) ≃* invSubmonoid M S :=
  ((M.map (algebraMap R S)).leftInvEquiv (submonoid_map_le_is_unit M S)).symm

noncomputable def toInvSubmonoid : M →* invSubmonoid M S :=
  (equivInvSubmonoid M S).toMonoidHom.comp ((algebraMap R S : R →* S).submonoidMap M)

theorem toInvSubmonoid_surjective : Function.Surjective (toInvSubmonoid M S) :=
  Function.Surjective.comp (β := M.map (algebraMap R S))
    (Equiv.surjective (equivInvSubmonoid _ _).toEquiv) (MonoidHom.submonoidMap_surjective _ _)
