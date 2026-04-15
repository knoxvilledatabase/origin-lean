/-
Extracted from Geometry/Euclidean/NinePointCircle.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Nine-point circle

This file defines the nine-point circle of a triangle, and its higher dimension analogue, the
3(n+1)-point sphere of a simplex. Specifically for triangles, we show that it passes through nine
specific points as desired.

## Main definitions
* `Affine.Simplex.ninePointCircle`: the 3(n+1)-point sphere of a simplex.
* `Affine.Simplex.eulerPoint`: the $1/n$th of the way from the Monge point to a vertex.
* `Affine.Simplex.faceOppositeCentroid_mem_ninePointCircle`: the 3(n+1)-point sphere passes through
  the centroid of each face of the simplex
* `Affine.Simplex.eulerPoint_mem_ninePointCircle`: the 3(n+1)-point sphere passes through all Euler
  points.
* `Affine.Triangle.altitudeFoot_mem_ninePointCircle`: the nine-point circle passes through all
  three altitude feet of the triangle.

## References
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)
-/

noncomputable section

open AffineSubspace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

def ninePointCircle {n : ℕ} (s : Simplex ℝ P n) : Sphere P where
  center := ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : ℝ)

theorem ninePointCircle_center_mem_affineSpan {n : ℕ} (s : Simplex ℝ P n) :
    s.ninePointCircle.center ∈ affineSpan ℝ (Set.range s.points) := by
  rw [ninePointCircle_center]
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ s.circumcenter_mem_affineSpan
  apply Submodule.smul_mem
  exact AffineSubspace.vsub_mem_direction s.centroid_mem_affineSpan s.circumcenter_mem_affineSpan
