/-
Extracted from RingTheory/GradedAlgebra/Homogeneous/Ideal.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `GradedRing 𝒜` where `𝒜 : ι → Submodule R A` and
operations on them.

## Main definitions

For any `I : Ideal A`:
* `Ideal.IsHomogeneous 𝒜 I`: The property that an ideal is closed under `GradedRing.proj`.
* `HomogeneousIdeal 𝒜`: The structure extending ideals which satisfy `Ideal.IsHomogeneous`.
* `Ideal.homogeneousCore I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `Ideal.homogeneousHull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `HomogeneousIdeal.completeLattice`: `Ideal.IsHomogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `Ideal.homogeneousCore.gi`: `Ideal.homogeneousCore` forms a Galois insertion with coercion.
* `Ideal.homogeneousHull.gi`: `Ideal.homogeneousHull` forms a Galois insertion with coercion.

## Implementation notes

We introduce `Ideal.homogeneousCore'` earlier than might be expected so that we can get access
to `Ideal.IsHomogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

open SetLike DirectSum Set

open Pointwise DirectSum

variable {ι σ A : Type*}

section HomogeneousDef

variable [Semiring A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

variable (I : Ideal A)

abbrev Ideal.IsHomogeneous : Prop := Submodule.IsHomogeneous I 𝒜

theorem Ideal.IsHomogeneous.mem_iff {I} (hI : Ideal.IsHomogeneous 𝒜 I) {x} :
    x ∈ I ↔ ∀ i, (decompose 𝒜 x i : A) ∈ I :=
  AddSubmonoidClass.IsHomogeneous.mem_iff 𝒜 _ hI

abbrev HomogeneousIdeal := HomogeneousSubmodule 𝒜 𝒜

variable {𝒜}

abbrev HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule
