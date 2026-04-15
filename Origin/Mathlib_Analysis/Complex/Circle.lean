/-
Extracted from Analysis/Complex/Circle.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# The circle

This file defines `Circle` to be the metric sphere (`Metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `Circle.exp` to be the natural map `fun t ↦ exp (t * I)` from `ℝ` to
`Circle`, and show that this map is a group homomorphism.

We define two additive characters onto the circle:
* `Real.fourierChar`: The character `fun x ↦ exp ((2 * π * x) * I)` (for which we introduce the
  notation `𝐞` in the scope `FourierTransform`). This uses the analyst convention that there is a
  `2 * π` in the exponent.
* `Real.probChar`: The character `fun x ↦ exp (x * I)`, which uses the probabilist convention that
  there is no `2 * π` in the exponent.

## Implementation notes

Because later (in `Geometry.Manifold.Instances.Sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `Metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/

noncomputable section

open Complex Function Metric ComplexConjugate

def Circle : Type := Submonoid.unitSphere ℂ

deriving TopologicalSpace

namespace Circle

variable {x y : Circle}

-- INSTANCE (free from Core): instCoeOut

-- INSTANCE (free from Core): instCommGroup

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instMetricSpace
