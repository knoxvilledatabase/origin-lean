/-
Extracted from GroupTheory/MonoidLocalization/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M` such that `f x = f y`, there exists `c ∈ S` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

Given such a localization map `f : M →* N`, we can define the surjection
`Submonoid.LocalizationMap.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`. Mapping properties
of the localization (e.g. extending a map from `M → P` to `N` if the image of `S` is contained in
the units) are treated in a later file `Mathlib.GroupTheory.MonoidLocalization.Maps`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `Localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

The Grothendieck group construction corresponds to localizing at the top submonoid, namely making
every element invertible.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To reason about the localization as a quotient type, use `mk_eq_monoidOf_mk'` and associated
lemmas. These show the quotient map `mk : M → S → Localization S` equals the
surjection `LocalizationMap.mk'` induced by the map
`Localization.monoidOf : Submonoid.LocalizationMap S (Localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoidOf_mk'` hence gives you access to the results in the rest of the file, which are about
the `LocalizationMap.mk'` induced by any localization map.

## TODO

* Show that the localization at the top monoid is a group.
* Generalise to (nonempty) subsemigroups.
* If we acquire more bundlings, we can make `Localization.mkOrderEmbedding` be an ordered monoid
  embedding.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

assert_not_exists MonoidWithZero Ring

open Function

namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M] (S : AddSubmonoid M) (N : Type*) [AddCommMonoid N]

variable {N} in

structure IsLocalizationMap (S : AddSubmonoid M) (f : M → N) where
  map_addUnits (y : S) : IsAddUnit (f y)
  surj (z : N) : ∃ x : M × S, z + f x.2 = f x.1
  exists_of_eq {x y} : f x = f y → ∃ c : S, c + x = c + y

structure LocalizationMap extends M →ₙ+ N where
  isLocalizationMap : IsLocalizationMap S toFun

add_decl_doc LocalizationMap.toAddHom

end AddSubmonoid

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace Submonoid

variable {N} in
