/-
Extracted from Analysis/Analytic/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `HasFPowerSeriesOnBall f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `HasFPowerSeriesAt f p x`: on some ball of center `x` with positive radius, holds
  `HasFPowerSeriesOnBall f p x r`.
* `AnalyticAt 𝕜 f x`: there exists a power series `p` such that holds `HasFPowerSeriesAt f p x`.
* `AnalyticOnNhd 𝕜 f s`: the function `f` is analytic at every point of `s`.

We also define versions of `HasFPowerSeriesOnBall`, `AnalyticAt`, and `AnalyticOnNhd` restricted to
a set, similar to `ContinuousWithinAt`.
See `Mathlib/Analysis/Analytic/Within.lean` for basic properties.

* `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s ∪ {x}] x`.
* `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `HasFPowerSeriesOnBall.continuousOn` and `HasFPowerSeriesAt.continuousAt` and
  `AnalyticAt.continuousAt`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `FormalMultilinearSeries.hasFPowerSeriesOnBall`.

-/

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Topology NNReal Filter ENNReal Set Asymptotics

open scoped Pointwise

/-! ### Expanding a function as a power series -/

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

structure HasFPowerSeriesOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : ℝ≥0∞) :
    Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum :
    ∀ {y}, y ∈ Metric.eball (0 : E) r → HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

structure HasFPowerSeriesWithinOnBall (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
    (x : E) (r : ℝ≥0∞) : Prop where
  /-- `p` converges on `ball 0 r` -/
  r_le : r ≤ p.radius
  /-- The radius of convergence is positive -/
  r_pos : 0 < r
  /-- `p converges to f` within `s` -/
  hasSum : ∀ {y}, x + y ∈ insert x s → y ∈ Metric.eball (0 : E) r →
    HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y))

def HasFPowerSeriesAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  ∃ r, HasFPowerSeriesOnBall f p x r

def HasFPowerSeriesWithinAt (f : E → F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E) :=
  ∃ r, HasFPowerSeriesWithinOnBall f p s x r

attribute [bound_forward] HasFPowerSeriesOnBall.r_pos HasFPowerSeriesWithinOnBall.r_pos

variable (𝕜)
