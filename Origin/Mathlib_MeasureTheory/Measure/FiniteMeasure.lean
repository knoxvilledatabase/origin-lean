/-
Extracted from MeasureTheory/Measure/FiniteMeasure.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finite measures

This file defines the type of finite measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of finite measures is equipped with the topology of weak convergence
of measures. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

## Main definitions

The main definitions are
* `MeasureTheory.FiniteMeasure Ω`: The type of finite measures on `Ω` with the topology of weak
  convergence of measures.
* `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`:
  Interpret a finite measure as a continuous linear functional on the space of
  bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
  topology of weak convergence.
* `MeasureTheory.FiniteMeasure.map`: The push-forward `f* μ` of a finite measure `μ` on `Ω`
  along a measurable function `f : Ω → Ω'`.
* `MeasureTheory.FiniteMeasure.mapCLM`: The push-forward along a given continuous `f : Ω → Ω'`
  as a continuous linear map `f* : FiniteMeasure Ω →L[ℝ≥0] FiniteMeasure Ω'`.

## Main results

* Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
  bounded continuous nonnegative functions on `Ω` via integration:
  `MeasureTheory.FiniteMeasure.toWeakDualBCNN : FiniteMeasure Ω → (WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0))`
* `MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
  measures is characterized by the convergence of integrals of all bounded continuous functions.
  This shows that the chosen definition of topology coincides with the common textbook definition
  of weak convergence of measures. A similar characterization by the convergence of integrals (in
  the `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative functions is
  `MeasureTheory.FiniteMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of finite measures `f* : FiniteMeasure Ω → FiniteMeasure Ω'` is continuous.
* `MeasureTheory.FiniteMeasure.t2Space`: The topology of weak convergence of finite Borel measures
  is Hausdorff on spaces where indicators of closed sets have continuous decreasing approximating
  sequences (in particular on any pseudo-metrizable spaces).

## Implementation notes

The topology of weak convergence of finite Borel measures is defined using a mapping from
`MeasureTheory.FiniteMeasure Ω` to `WeakDual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The implementation of `MeasureTheory.FiniteMeasure Ω` and is directly as a subtype of
`MeasureTheory.Measure Ω`, and the coercion to a function is the composition `ENNReal.toNNReal`
and the coercion to function of `MeasureTheory.Measure Ω`. Another alternative would have been to
use a bijection with `MeasureTheory.VectorMeasure Ω ℝ≥0` as an intermediate step. Some
considerations:
* Potential advantages of using the `NNReal`-valued vector measure alternative:
  * The coercion to function would avoid need to compose with `ENNReal.toNNReal`, the
    `NNReal`-valued API could be more directly available.
* Potential drawbacks of the vector measure alternative:
  * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
    have measure 0.
  * No integration theory directly. E.g., the topology definition requires
    `MeasureTheory.lintegral` w.r.t. a coercion to `MeasureTheory.Measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure

-/

noncomputable section

open BoundedContinuousFunction Filter MeasureTheory Set Topology

open scoped ENNReal NNReal Function

namespace MeasureTheory

namespace FiniteMeasure

section FiniteMeasure

/-! ### Finite measures

In this section we define the `Type` of `MeasureTheory.FiniteMeasure Ω`, when `Ω` is a measurable
space. Finite measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.FiniteMeasure Ω` is equipped with
the topology of weak convergence of measures. This is implemented by defining a pairing of finite
measures `μ` on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration,
and using the associated weak topology (essentially the weak-star topology on the dual of
`Ω →ᵇ ℝ≥0`).
-/

variable {Ω : Type*} [MeasurableSpace Ω] {s t : Set Ω}

def _root_.MeasureTheory.FiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsFiniteMeasure μ }
