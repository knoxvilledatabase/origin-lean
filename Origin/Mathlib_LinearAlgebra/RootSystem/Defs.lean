/-
Extracted from LinearAlgebra/RootSystem/Defs.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Root data and root systems

This file contains basic definitions for root systems and root data.

## Main definitions:

* `RootPairing`: Given two perfectly-paired `R`-modules `M` and `N` (over some commutative ring
  `R`) a root pairing with indexing set `ι` is the data of an `ι`-indexed subset of `M`
  ("the roots") an `ι`-indexed subset of `N` ("the coroots"), and an `ι`-indexed set of
  permutations of `ι` such that each root-coroot pair evaluates to `2`, and the permutation
  attached to each element of `ι` is compatible with the reflections on the corresponding roots and
  coroots.
* `RootDatum`: A root datum is a root pairing for which the roots and coroots take values in
  finitely-generated free Abelian groups.
* `RootSystem`: A root system is a root pairing for which the roots span their ambient module.

## Implementation details

A root datum is sometimes defined as two subsets: roots and coroots, together with a bijection
between them, subject to hypotheses. However the hypotheses ensure that the bijection is unique and
so the question arises of whether this bijection should be part of the data of a root datum or
whether one should merely assert its existence. For root systems, things are even more extreme: the
coroots are uniquely determined by the roots. Furthermore a root system induces a canonical
non-degenerate bilinear form on the ambient space and many informal accounts even include this form
as part of the data.

We have opted for a design in which some of the uniquely-determined data is included: the bijection
between roots and coroots is (implicitly) included and the coroots are included for root systems.
Empirically this seems to be by far the most convenient design and by providing extensionality
lemmas expressing the uniqueness we expect to get the best of both worlds.

Furthermore, we require roots and coroots to be injections from a base indexing type `ι` rather than
subsets of their codomains. This design was chosen to avoid the bijection between roots and coroots
being a dependently-typed object. A third option would be to have the roots and coroots be subsets
but to avoid having a dependently-typed bijection by defining it globally with junk value `0`
outside of the roots and coroots. This would work but lacks the convenient symmetry that the chosen
design enjoys: by introducing the indexing type `ι`, one does not have to pick a direction
(`roots → coroots` or `coroots → roots`) for the forward direction of the bijection. Besides,
providing the user with the additional definitional power to specify an indexing type `ι` is a
benefit and the junk-value pattern is a cost.

As a final point of divergence from the classical literature, we make the reflection permutation on
roots and coroots explicit, rather than specifying only that reflection preserves the sets of roots
and coroots. This is necessary when working with infinite root systems, where the coroots are not
uniquely determined by the roots, because without it, the reflection permutations on roots and
coroots may not correspond. For this purpose, we define a map from `ι` to permutations on `ι`, and
require that it is compatible with reflections and coreflections.

-/

open Set Function

open Module hiding reflection

open Submodule (span span_image)

open AddSubgroup (zmultiples)

noncomputable section

variable (ι R M N : Type*)
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure RootPairing extends M →ₗ[R] N →ₗ[R] R where
  [isPerfPair_toLinearMap : toLinearMap.IsPerfPair]
  /-- A parametrized family of vectors, called roots. -/
  root : ι ↪ M
  /-- A parametrized family of dual vectors, called coroots. -/
  coroot : ι ↪ N
  root_coroot_two : ∀ i, toLinearMap (root i) (coroot i) = 2
  /-- A parametrized family of permutations, induced by reflections. This corresponds to the
  classical requirement that the symmetry attached to each root (later defined in
  `RootPairing.reflection`) leave the whole set of roots stable: as explained above, we
  formalize this stability by fixing the image of the roots through each reflection (whence the
  permutation); and similarly for coroots. -/
  reflectionPerm : ι → (ι ≃ ι)
  reflectionPerm_root : ∀ i j,
    root j - toLinearMap (root j) (coroot i) • root i = root (reflectionPerm i j)
  reflectionPerm_coroot : ∀ i j,
    coroot j - toLinearMap (root i) (coroot j) • coroot i = coroot (reflectionPerm i j)

attribute [instance] RootPairing.isPerfPair_toLinearMap

abbrev RootDatum (X₁ X₂ : Type*) [AddCommGroup X₁] [AddCommGroup X₂] := RootPairing ι ℤ X₁ X₂

namespace RootPairing

variable {ι R M N}

variable (P : RootPairing ι R M N) (i j : ι)

class IsRootSystem : Prop where
  span_root_eq_top : span R (range P.root) = ⊤
  span_coroot_eq_top : span R (range P.coroot) = ⊤
