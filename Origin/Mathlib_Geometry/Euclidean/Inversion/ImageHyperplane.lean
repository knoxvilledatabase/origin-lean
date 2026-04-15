/-
Extracted from Geometry/Euclidean/Inversion/ImageHyperplane.lean
Genuine: 1 of 9 | Dissolved: 8 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Image of a hyperplane under inversion

In this file we prove that the inversion with center `c` and radius `R ≠ 0` maps a sphere passing
through the center to a hyperplane, and vice versa. More precisely, it maps a sphere with center
`y ≠ c` and radius `dist y c` to the hyperplane
`AffineSubspace.perpBisector c (EuclideanGeometry.inversion c R y)`.

The exact statements are a little more complicated because `EuclideanGeometry.inversion c R` sends
the center to itself, not to a point at infinity.

We also prove that the inversion sends an affine subspace passing through the center to itself.

## Keywords

inversion
-/

open Metric Function AffineMap Set AffineSubspace

open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {c x y : P} {R : ℝ}

namespace EuclideanGeometry

-- DISSOLVED: inversion_mem_perpBisector_inversion_iff

-- DISSOLVED: inversion_mem_perpBisector_inversion_iff'

-- DISSOLVED: preimage_inversion_perpBisector_inversion

-- DISSOLVED: preimage_inversion_perpBisector

-- DISSOLVED: image_inversion_perpBisector

-- DISSOLVED: preimage_inversion_sphere_dist_center

-- DISSOLVED: image_inversion_sphere_dist_center

theorem mapsTo_inversion_affineSubspace_of_mem {p : AffineSubspace ℝ P} (hp : c ∈ p) :
    MapsTo (inversion c R) p p := fun _ ↦ AffineMap.lineMap_mem _ hp

-- DISSOLVED: image_inversion_affineSubspace_of_mem

end EuclideanGeometry
