/-
Extracted from NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean
Genuine: 7 of 8 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fundamental Cone: set of elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that it is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

1. since `NormLeOne K` is norm-stable, in the sense that
  `normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K))`,
  see `normLeOne_eq_preimage_image`, it's enough to study the subset
  `normAtAllPlaces '' (normLeOne K)` of `realSpace K`.

2. A description of `normAtAllPlaces '' (normLeOne K)` is given by `normAtAllPlaces_normLeOne`, it
  is the set of `x : realSpace K`, nonnegative at all places, whose norm is nonzero and `≤ 1` and
  such that `logMap x` is in the `fundamentalDomain` of `basisUnitLattice K`.
  Note that, here and elsewhere, we identify `x` with its image in `mixedSpace K` given
  by `mixedSpaceOfRealSpace x`.

3. In order to describe the inverse image in `realSpace K` of the `fundamentalDomain` of
  `basisUnitLattice K`, we define the map `expMap : realSpace K → realSpace K` that is, in
  some way, the right inverse of `logMap`, see `logMap_expMap`.

4. Denote by `ηᵢ` (with `i ≠ w₀` where `w₀` is the distinguished infinite place,
  see the description of `logSpace` below) the fundamental system of units given by
  `fundSystem` and let `|ηᵢ|` denote `normAtAllPlaces (mixedEmbedding ηᵢ)`, that is the vector
  `(w (ηᵢ))_w` in `realSpace K`. Then, the image of `|ηᵢ|` by `expMap.symm` form a basis of the
  subspace `{x : realSpace K | ∑ w, x w = 0}`. We complete by adding the vector `(mult w)_w` to
  get a basis, called `completeBasis`, of `realSpace K`. The basis `completeBasis K` has
  the property that, for `i ≠ w₀`, the image of `completeBasis K i` by the
  natural restriction map `realSpace K → logSpace K` is `basisUnitLattice K`.

5. At this point, we can construct the map `expMapBasis` that plays a crucial part in the proof.
  It is the map that sends `x : realSpace K` to `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i`, see
  `expMapBasis_apply'`. Then, we prove a change of variable formula for `expMapBasis`, see
  `setLIntegral_expMapBasis_image`.

6. We define a set `paramSet` in `realSpace K` and prove that
  `normAtAllPlaces '' (normLeOne K) = expMapBasis (paramSet K)`, see
  `normAtAllPlaces_normLeOne_eq_image`. Using this, `setLIntegral_expMapBasis_image` and the results
  from `mixedEmbedding.polarCoord`, we can then compute the volume of `normLeOne K`, see
  `volume_normLeOne`.

7. Finally, we need to prove that the frontier of `normLeOne K` has zero-volume (we will prove
  in passing that `normLeOne K` is bounded.) For that we prove that
  `volume (interior (normLeOne K)) = volume (closure (normLeOne K))`, see
  `volume_interior_eq_volume_closure`. Since we know that the volume of `interior (normLeOne K)` is
  finite since it is bounded by the volume of `normLeOne K`, the result follows, see
  `volume_frontier_normLeOne`. We proceed in several steps.

  7.1. We prove first that
    `normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K)`, see
    `subset_interior_normLeOne` (Note that here again we identify `realSpace K` with its image
    in `mixedSpace K`). The main argument is that `expMapBasis` is an open partial homeomorphism
    and that `interior (paramSet K)` is a subset of its source, so its image by `expMapBasis`
    is still open.

  7.2. The same kind of argument does not work with `closure (paramSet)` since it is not contained
    in the source of `expMapBasis`. So we define a compact set, called `compactSet K`, such that
    `closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K)`, see `closure_normLeOne_subset`,
    and it is almost equal to `expMapBasis '' closure (paramSet K)`, see `compactSet_ae`.

  7.3. We get from the above that `normLeOne K ⊆ normAtAllPlaces⁻¹' (compactSet K)`, from which
    it follows easily that `normLeOne K` is bounded, see `isBounded_normLeOne`.

  7.4. Finally, we prove that `volume (normAtAllPlaces ⁻¹' compactSet K) =
    volume (normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K)))`, which implies that
    `volume (interior (normLeOne K)) = volume (closure (normLeOne K))` by the above and the fact
    that `volume (interior (normLeOne K)) ≤ volume (closure (normLeOne K))`, which boils down to
    the fact that the interior and closure of `paramSet K` are almost equal, see
    `closure_paramSet_ae_interior`.

## Spaces and maps

To help understand the proof, we make a list of (almost) all the spaces and maps used and
their connections (as hinted above, we do not mention the map `mixedSpaceOfRealSpace` since we
identify `realSpace K` with its image in `mixedSpace K`).

* `mixedSpace`: the set `({w // IsReal w} → ℝ) × (w // IsComplex w → ℂ)` where `w` denote the
  infinite places of `K`.

* `realSpace`: the set `w → ℝ` where `w` denote the infinite places of `K`

* `logSpace`: the set `{w // w ≠ w₀} → ℝ` where `w₀` is a distinguished place of `K`. It is the set
  used in the proof of Dirichlet Unit Theorem.

* `mixedEmbedding : K → mixedSpace K`: the map that sends `x : K` to `φ_w(x)` where, for all
  infinite place `w`, `φ_w : K → ℝ` or `ℂ`, resp. if `w` is real or if `w` is complex, denote a
  complex embedding associated to `w`.

* `logEmbedding : (𝓞 K)ˣ → logSpace K`: the map that sends the unit `u : (𝓞 K)ˣ` to
  `(mult w * log (w u))_w` for `w ≠ w₀`. Its image is `unitLattice K`, a `ℤ`-lattice of
  `logSpace K`, that admits `basisUnitLattice K` as a basis.

* `logMap : mixedSpace K → logSpace K`: this map is defined such that it factors `logEmbedding`,
  that is, for `u : (𝓞 K)ˣ`, `logMap (mixedEmbedding x) = logEmbedding x`, and that
  `logMap (c • x) = logMap x` for `c ≠ 0` and `norm x ≠ 0`. The inverse image of the fundamental
  domain of `basisUnitLattice K` by `logMap` (minus the elements of norm zero) is
  `fundamentalCone K`.

* `expMap : realSpace K → realSpace K`: the right inverse of `logMap` in the sense that
  `logMap (expMap x) = (x_w)_{w ≠ w₀}`.

* `expMapBasis : realSpace K → realSpace K`: the map that sends `x : realSpace K` to
  `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
  by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`.

-/

variable (K : Type*) [Field K]

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

  NumberField.Units dirichletUnitTheorem

namespace NumberField.mixedEmbedding.fundamentalCone

section normAtAllPlaces

variable [NumberField K]

variable {K}

theorem logMap_normAtAllPlaces (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w ↦ by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

theorem norm_normAtAllPlaces (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

theorem normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_diff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_setOf_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section normLeOne_def

variable [NumberField K]

abbrev normLeOne : Set (mixedSpace K) := fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1}

variable {K} in

theorem mem_normLeOne {x : mixedSpace K} :
    x ∈ normLeOne K ↔ x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1 := Set.mem_sep_iff

theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem normLeOne_eq_preimage_image :
    normLeOne K = normAtAllPlaces ⁻¹' (normAtAllPlaces '' (normLeOne K)) := by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne, ← normAtAllPlaces_mem_fundamentalCone_iff, ← norm_normAtAllPlaces,
    ← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

open scoped Classical in

-- DISSOLVED: normAtAllPlaces_normLeOne

end normLeOne_def

noncomputable section expMap

variable {K}
