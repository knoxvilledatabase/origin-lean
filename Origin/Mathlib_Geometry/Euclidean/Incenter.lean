/-
Extracted from Geometry/Euclidean/Incenter.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Incenters and excenters of simplices.

This file defines the insphere and exspheres of a simplex (tangent to the faces of the simplex),
and the center and radius of such spheres.

The terms "exsphere", "excenter" and "exradius" are used in this file in a general sense where
a `Finset` `signs` of indices is given that determine, up to negating all the signs, which
vertices of the simplex lie on the same side of the opposite face as the excenter and which lie
on the opposite side of that face. This includes the cases of the insphere, incenter and
inradius, when `signs` is `∅` (or `univ`); the insphere always exists. It also includes the case
of an exsphere opposite a vertex, when `signs` is a singleton (or its complement), which always
exists in two or more dimensions. In three or more dimensions, there are further possibilities
for `signs`, and the corresponding excenters may or may not exist, depending on the choice of
simplex. For convenience, the most common definitions `exsphere`, `excenter` and `exradius` have
corresponding `insphere`, `incenter` and `inradius` definitions, and various lemmas are duplicated
for the case of the insphere to avoid needing to pass an `ExcenterExists` hypothesis in that case.
However, other definitions such as `excenterWeights`, `touchpoint` and `touchpointWeights` are not
duplicated.

## Main definitions

* `Affine.Simplex.ExcenterExists` says whether an excenter exists with a given set of indices.
* `Affine.Simplex.excenterWeights` are the weights of the excenter with the given set of
  indices, if it exists, as an affine combination of the vertices.
* `Affine.Simplex.exsphere` is the exsphere with the given set of indices, if it exists, with
  shorthands:
  * `Affine.Simplex.excenter` for the center of this sphere
  * `Affine.Simplex.exradius` for the radius of this sphere
* `Affine.Simplex.insphere` is the insphere, with shorthands:
  * `Affine.Simplex.incenter` for the center of this sphere
  * `Affine.Simplex.inradius` for the radius of this sphere
* `Affine.Simplex.touchpoint` for the point where an exsphere of a simplex is tangent to one of
  the faces.
* `Affine.Simplex.touchpointWeights` for the weights of a touchpoint as an affine combination of
  the vertices.

## References

* https://en.wikipedia.org/wiki/Incircle_and_excircles
* https://en.wikipedia.org/wiki/Incenter

-/

open EuclideanGeometry

open scoped Finset RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]

variable [NormedAddTorsor V₂ P₂]

noncomputable section

namespace Affine

namespace Simplex

variable {m n : ℕ} [NeZero m] [NeZero n] (s : Simplex ℝ P n)

def excenterWeightsUnnorm (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : ℝ :=
  (if i ∈ signs then -1 else 1) * (s.height i)⁻¹

lemma excenterWeightsUnnorm_reindex (e : Fin (n + 1) ≃ Fin (m + 1)) (signs : Finset (Fin (m + 1))) :
    (s.reindex e).excenterWeightsUnnorm signs =
      s.excenterWeightsUnnorm (signs.map e.symm) ∘ e.symm := by
  ext i
  simp [excenterWeightsUnnorm]
