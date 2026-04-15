/-
Extracted from Geometry/Euclidean/Angle/Unoriented/Affine.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Angles between points

This file defines unoriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.angle`, with notation `∠`, is the undirected angle determined by three
  points.
-/

noncomputable section

open Real RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {p p₀ : P}

nonrec def angle (p₁ p₂ p₃ : P) : ℝ :=
  angle (p₁ -ᵥ p₂ : V) (p₃ -ᵥ p₂)
