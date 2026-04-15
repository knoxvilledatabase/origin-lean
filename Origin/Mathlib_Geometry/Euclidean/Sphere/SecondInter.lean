/-
Extracted from Geometry/Euclidean/Sphere/SecondInter.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `EuclideanGeometry.Sphere.secondInter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]

variable [NormedAddTorsor V₂ P₂]

def Sphere.secondInter (s : Sphere P) (p : P) (v : V) : P :=
  (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p
