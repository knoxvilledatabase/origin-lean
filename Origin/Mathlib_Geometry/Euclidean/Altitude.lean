/-
Extracted from Geometry/Euclidean/Altitude.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Altitudes of a simplex

This file defines the altitudes of a simplex and their feet.

## Main definitions

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `altitudeFoot` is the orthogonal projection of a vertex of a simplex onto the opposite face.

* `height` is the distance between a vertex of a simplex and its `altitudeFoot`.

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>

-/

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]

variable [NormedAddTorsor V₂ P₂]

def altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)
