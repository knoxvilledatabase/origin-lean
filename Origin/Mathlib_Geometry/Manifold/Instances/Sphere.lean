/-
Extracted from Geometry/Manifold/Instances/Sphere.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put an analytic manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, an open partial homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal
complement of `v`).

For finite-dimensional `E`, we then construct an analytic manifold instance on the sphere; the
charts here are obtained by composing the open partial homeomorphisms `stereographic` with arbitrary
isometries from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about `C^n` maps:
* `contMDiff_coe_sphere` states that the coercion map from the sphere into `E` is analytic;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `contMDiff.codRestrict_sphere` states that a map from a manifold into the sphere is
  `C^m` if its lift to a map to `E` is `C^m`; this is a useful tool for constructing `C^m` maps
  *to* the sphere.

As an application we prove `contMDiffNegSphere`, that the antipodal map is analytic.

Finally, we equip the `Circle` (defined in `Analysis.Complex.Circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `EuclideanSpace ℝ (Fin 1)` (inherited from `Metric.Sphere`)
* an analytic Lie group with model with corners `𝓡 1`

We furthermore show that `Circle.exp` (defined in `Analysis.Complex.Circle` to be the natural
map `fun t ↦ exp (t * I)` from `ℝ` to `Circle`) is analytic.


## Implementation notes

The model space for the charted space instance is `EuclideanSpace ℝ (Fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `EuclideanSpace ℝ (Fin (2 - 1))` but not with model space
`EuclideanSpace ℝ (Fin 1)`.

## TODO

Relate the stereographic projection to the inversion of the space.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

open Metric Module Function

open scoped Manifold ContDiff RealInnerProductSpace

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/

def stereoToFun (x : E) : (ℝ ∙ v)ᗮ :=
  (2 / ((1 : ℝ) - innerSL ℝ v x)) • (ℝ ∙ v)ᗮ.orthogonalProjection x

variable {v}
