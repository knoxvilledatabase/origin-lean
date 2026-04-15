/-
Extracted from Geometry/Manifold/BumpFunction.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Smooth bump functions on a smooth manifold

In this file we define `SmoothBumpFunction I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < rIn < rOut` with small enough `rOut`.
We define a coercion to function for this type, and for `f : SmoothBumpFunction I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed ball of radius `f.rIn` centered at `c`;
* `f x = 0` outside of the ball of radius `f.rOut` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `extChartAt I f` and are given as lemmas in the
`SmoothBumpFunction` namespace.

## Tags

manifold, smooth bump function
-/

universe uE uF uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

open Function Filter Module Set Metric

open scoped Topology Manifold ContDiff

noncomputable section

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

variable (I) in

structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c) where
  closedBall_subset : closedBall (extChartAt I c c) rOut ∩ range I ⊆ (extChartAt I c).target

namespace SmoothBumpFunction

section FiniteDimensional

variable [FiniteDimensional ℝ E]

variable {c : M} (f : SmoothBumpFunction I c) {x : M}
