/-
Extracted from RingTheory/Localization/Basic.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localizations of commutative rings

This file contains various basic results on localizations.

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

* `IsLocalization.algEquiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
  are isomorphic as `R`-algebras

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

assert_not_exists Ideal

open Function

namespace Localization

open IsLocalization

variable {ι : Type*} {R : ι → Type*} [∀ i, CommSemiring (R i)]

variable {i : ι} (S : Submonoid (R i))

noncomputable abbrev mapPiEvalRingHom :
    Localization (S.comap <| Pi.evalRingHom R i) →+* Localization S :=
  map (T := S) _ (Pi.evalRingHom R i) le_rfl

open Function in

theorem mapPiEvalRingHom_bijective : Bijective (mapPiEvalRingHom S) := by
  let T := S.comap (Pi.evalRingHom R i)
  classical
  refine ⟨fun x₁ x₂ eq ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨r₁, s₁, rfl⟩ := exists_mk'_eq T x₁
    obtain ⟨r₂, s₂, rfl⟩ := exists_mk'_eq T x₂
    simp_rw [map_mk'] at eq
    rw [IsLocalization.eq] at eq ⊢
    obtain ⟨s, hs⟩ := eq
    refine ⟨⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩, funext fun j ↦ ?_⟩
    obtain rfl | ne := eq_or_ne j i
    · simpa using hs
    · simp [update_of_ne ne]
  · obtain ⟨r, s, rfl⟩ := exists_mk'_eq S x
    exact ⟨mk' (M := T) _ (update 0 i r) ⟨update 0 i s, by apply update_self i s.1 0 ▸ s.2⟩,
      by simp [map_mk']⟩

end Localization

section CommSemiring

variable {R : Type*} [CommSemiring R] {M N : Submonoid R} {S : Type*} [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section IsLocalization

variable [IsLocalization M S]

include M in

variable (R M) in

protected lemma finite [Finite R] : Finite S := by
  have : Function.Surjective (Function.uncurry (mk' (M := M) S)) := fun x ↦ by
    simpa using IsLocalization.exists_mk'_eq M x
  exact .of_surjective _ this

section CompatibleSMul

variable (N₁ N₂ : Type*) [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]

variable (M S) in

include M in

theorem linearMap_compatibleSMul [Module S N₁] [Module S N₂]
    [IsScalarTower R S N₁] [IsScalarTower R S N₂] :
    LinearMap.CompatibleSMul N₁ N₂ S R where
  map_smul f s s' := by
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M s
    rw [← (map_units S m).smul_left_cancel]
    simp_rw [algebraMap_smul, ← map_smul, ← smul_assoc, smul_mk'_self, algebraMap_smul, map_smul]

-- INSTANCE (free from Core): [Module

end CompatibleSMul

variable {g : R →+* P} (hg : ∀ y : M, IsUnit (g y))

variable (M) in

include M in

theorem algHom_subsingleton [Algebra R P] : Subsingleton (S →ₐ[R] P) :=
  ⟨fun f g =>
    AlgHom.coe_ringHom_injective <|
      IsLocalization.ringHom_ext M <| by rw [f.comp_algebraMap, g.comp_algebraMap]⟩

section AlgEquiv

variable {Q : Type*} [CommSemiring Q] [Algebra R Q] [IsLocalization M Q]

variable (M S Q)
