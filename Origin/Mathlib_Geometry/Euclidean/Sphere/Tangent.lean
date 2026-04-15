/-
Extracted from Geometry/Euclidean/Sphere/Tangent.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tangency for spheres.

This file defines notions of spheres being tangent to affine subspaces and other spheres.

## Main definitions

* `EuclideanGeometry.Sphere.IsTangentAt`: the property of an affine subspace being tangent to a
  sphere at a given point.

* `EuclideanGeometry.Sphere.IsTangent`: the property of an affine subspace being tangent to a
  sphere at some point.

* `EuclideanGeometry.Sphere.tangentSet`: the set of all maximal tangent spaces to a given sphere.

* `EuclideanGeometry.Sphere.tangentsFrom`: the set of all maximal tangent spaces to a given
  sphere and containing a given point.

* `EuclideanGeometry.Sphere.commonTangents`: the set of all maximal common tangent spaces to two
  given spheres.

* `EuclideanGeometry.Sphere.commonIntTangents`: the set of all maximal common internal tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.commonExtTangents`: the set of all maximal common external tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.IsExtTangentAt`: the property of two spheres being externally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsIntTangentAt`: the property of two spheres being internally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsExtTangent`: the property of two spheres being externally tangent.

* `EuclideanGeometry.Sphere.IsIntTangent`: the property of two spheres being internally tangent.

-/

namespace EuclideanGeometry

namespace Sphere

open AffineSubspace RealInnerProductSpace

open scoped Affine

variable {V P : Type*}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

structure IsTangentAt (s : Sphere P) (p : P) (as : AffineSubspace ℝ P) : Prop where
  mem_sphere : p ∈ s
  mem_space : p ∈ as
  le_orthRadius : as ≤ s.orthRadius p
