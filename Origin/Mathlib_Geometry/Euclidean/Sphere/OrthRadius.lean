/-
Extracted from Geometry/Euclidean/Sphere/OrthRadius.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Spaces orthogonal to the radius vector in spheres.

This file defines the affine subspace orthogonal to the radius vector at a point.

## Main definitions

* `EuclideanGeometry.Sphere.orthRadius`: the affine subspace orthogonal to the radius vector at
  a point (the tangent space, if that point lies in the sphere; more generally, the polar of the
  inversion of that point in the sphere).

-/

namespace EuclideanGeometry

namespace Sphere

open AffineSubspace Function RealInnerProductSpace

open scoped Affine

variable {V P : Type*}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

noncomputable def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P :=
  .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ

-- INSTANCE (free from Core): (s
