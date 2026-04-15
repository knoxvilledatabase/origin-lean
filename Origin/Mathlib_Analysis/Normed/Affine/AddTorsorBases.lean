/-
Extracted from Analysis/Normed/Affine/AddTorsorBases.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

* `continuous_barycentric_coord`
* `isOpenMap_barycentric_coord`
* `AffineBasis.interior_convexHull`
* `IsOpen.exists_subset_affineIndependent_span_eq_top`
* `interior_convexHull_nonempty_iff_affineSpan_eq_top`
-/

assert_not_exists HasFDerivAt

section Barycentric

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable [MetricSpace P] [NormedAddTorsor E P]

theorem isOpenMap_barycentric_coord [Nontrivial ι] (b : AffineBasis ι 𝕜 P) (i : ι) :
    IsOpenMap (b.coord i) :=
  AffineMap.isOpenMap_linear_iff.mp <|
    (b.coord i).linear.isOpenMap_of_finiteDimensional <|
      (b.coord i).linear_surjective_iff.mpr (b.surjective_coord i)

variable [FiniteDimensional 𝕜 E] (b : AffineBasis ι 𝕜 P)
