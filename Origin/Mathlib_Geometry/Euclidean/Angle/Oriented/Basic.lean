/-
Extracted from Geometry/Euclidean/Angle/Oriented/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Oriented angles.

This file defines oriented angles in real inner product spaces.

## Main definitions

* `Orientation.oangle` is the oriented angle between two vectors with respect to an orientation.

## Implementation notes

The definitions here use the `Real.Angle` type, angles modulo `2 * π`. For some purposes,
angles modulo `π` are more convenient, because results are true for such angles with less
configuration dependence. Results that are only equalities modulo `π` can be represented
modulo `2 * π` as equalities of `(2 : ℤ) • θ`.

## References

* Evan Chen, Euclidean Geometry in Mathematical Olympiads.

-/

noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}

variable [NormedAddCommGroup V] [NormedAddCommGroup V']

variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']

variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "ω" => o.areaForm

def oangle (x y : V) : Real.Angle :=
  Complex.arg (o.kahler x y)
