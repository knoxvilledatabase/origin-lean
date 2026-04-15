/-
Extracted from Geometry/Euclidean/Angle/Oriented/Affine.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Oriented angles.

This file defines oriented angles in Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.oangle`, with notation `∡`, is the oriented angle determined by three
  points.

-/

noncomputable section

open Module Complex

open scoped Affine EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

abbrev o := @Module.Oriented.positiveOrientation

def oangle (p₁ p₂ p₃ : P) : Real.Angle :=
  o.oangle (p₁ -ᵥ p₂) (p₃ -ᵥ p₂)
