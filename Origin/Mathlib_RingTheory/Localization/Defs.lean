/-
Extracted from RingTheory/Localization/Defs.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R` such that `f x = f y`, there exists `c ∈ M` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variable (R S P Q : Type*) [CommRing R] [CommRing S] [CommRing P] [CommRing Q]
variable [Algebra R S] [Algebra P Q] (M : Submonoid R) (T : Submonoid P)
```

## Main definitions

* `IsLocalization (M : Submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
  localization of `R` at `M`, i.e. the canonical map `algebraMap R S : R →+* S` is a
  localization map (satisfying the above properties).
* `IsLocalization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
* `IsLocalization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
  which maps elements of `M` to invertible elements of the codomain.
* `IsLocalization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
  of `M` to elements of `T`
* `IsLocalization.ringEquivOfRingEquiv`: if `R` and `P` are isomorphic by an isomorphism
  sending `M` to `T`, then `S` and `Q` are isomorphic

## Main results

* `Localization M S`, a construction of the localization as a quotient type, defined in
  `GroupTheory.MonoidLocalization`, has `CommRing`, `Algebra R` and `IsLocalization M`
  instances if `R` is a ring. `Localization.Away`, `Localization.AtPrime` and `FractionRing`
  are abbreviations for `Localization`s and have their corresponding `IsLocalization` instances

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : LocalizationMap M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `IsLocalization` a predicate on the `algebraMap R S`,
we can ensure the localization map commutes nicely with other `algebraMap`s.

To prove most lemmas about a localization map `algebraMap R S` in this file we invoke the
corresponding proof for the underlying `CommMonoid` localization map
`IsLocalization.toLocalizationMap M S`, which can be found in `GroupTheory.MonoidLocalization`
and the namespace `Submonoid.LocalizationMap`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → Localization M` equals the surjection
`LocalizationMap.mk'` induced by the map `algebraMap : R →+* Localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `LocalizationMap.mk'` induced by any localization map.

The proof that "a `CommRing` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[Field K]` instead of just `[CommRing K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

assert_not_exists AlgHom Ideal

open Function

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

class IsLocalization' : Prop extends M.IsLocalizationMap (algebraMap R S)

abbrev IsLocalization := @IsLocalization'

theorem isLocalization_iff_isLocalizationMap :
    IsLocalization M S ↔ M.IsLocalizationMap (algebraMap R S) :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem isLocalization_iff : IsLocalization M S ↔
    (∀ y : M, IsUnit (algebraMap R S y)) ∧
    (∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1) ∧
    ∀ {x y : R}, algebraMap R S x = algebraMap R S y → ∃ c : M, c * x = c * y := by
  rw [isLocalization_iff_isLocalizationMap, Submonoid.isLocalizationMap_iff]

variable {M}

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

theorem map_units : ∀ y : M, IsUnit (algebraMap R S y) :=
  IsLocalization'.toIsLocalizationMap.map_units

variable (M) {S}

theorem surj : ∀ z : S, ∃ x : R × M, z * algebraMap R S x.2 = algebraMap R S x.1 :=
  IsLocalization'.toIsLocalizationMap.surj

variable {M} in

theorem exists_of_eq {x y : R} : algebraMap R S x = algebraMap R S y → ∃ c : M, c * x = c * y :=
  IsLocalization'.toIsLocalizationMap.exists_of_eq

variable (S)

variable {M} in

theorem smul_bijective (m : M) : Bijective fun s : S ↦ m • s := by
  simpa only [Submonoid.smul_def, Algebra.smul_def] using (map_units S m).smul_bijective

abbrev toLocalizationMap : M.LocalizationMap S where
  __ := algebraMap R S
  toFun := algebraMap R S
  isLocalizationMap := IsLocalization'.toIsLocalizationMap
