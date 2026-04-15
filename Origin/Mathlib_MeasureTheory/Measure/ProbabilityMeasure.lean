/-
Extracted from MeasureTheory/Measure/ProbabilityMeasure.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Probability measures

This file defines the type of probability measures on a given measurable space. When the underlying
space has a topology and the measurable space structure (sigma algebra) is finer than the Borel
sigma algebra, then the type of probability measures is equipped with the topology of convergence
in distribution (weak convergence of measures). The topology of convergence in distribution is the
coarsest topology w.r.t. which for every bounded continuous `ℝ≥0`-valued random variable `X`, the
expected value of `X` depends continuously on the choice of probability measure. This is a special
case of the topology of weak convergence of finite measures.

## Main definitions

The main definitions are
* the type `MeasureTheory.ProbabilityMeasure Ω` with the topology of convergence in
  distribution (a.k.a. convergence in law, weak convergence of measures);
* `MeasureTheory.ProbabilityMeasure.toFiniteMeasure`: Interpret a probability measure as
  a finite measure;
* `MeasureTheory.FiniteMeasure.normalize`: Normalize a finite measure to a probability measure
  (returns junk for the zero measure).
* `MeasureTheory.ProbabilityMeasure.map`: The push-forward `f* μ` of a probability measure
  `μ` on `Ω` along a measurable function `f : Ω → Ω'`.

## Main results

* `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`: Convergence of
  probability measures is characterized by the convergence of expected values of all bounded
  continuous random variables. This shows that the chosen definition of topology coincides with
  the common textbook definition of convergence in distribution, i.e., weak convergence of
  measures. A similar characterization by the convergence of expected values (in the
  `MeasureTheory.lintegral` sense) of all bounded continuous nonnegative random variables is
  `MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto`.
* `MeasureTheory.FiniteMeasure.tendsto_normalize_iff_tendsto`: The convergence of finite
  measures to a nonzero limit is characterized by the convergence of the probability-normalized
  versions and of the total masses.
* `MeasureTheory.ProbabilityMeasure.continuous_map`: For a continuous function `f : Ω → Ω'`, the
  push-forward of probability measures `f* : ProbabilityMeasure Ω → ProbabilityMeasure Ω'` is
  continuous.
* `MeasureTheory.ProbabilityMeasure.t2Space`: The topology of convergence in distribution is
  Hausdorff on Borel spaces where indicators of closed sets have continuous decreasing
  approximating sequences (in particular on any pseudo-metrizable spaces).

TODO:
* Probability measures form a convex space.

## Implementation notes

The topology of convergence in distribution on `MeasureTheory.ProbabilityMeasure Ω` is inherited
weak convergence of finite measures via the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.

Like `MeasureTheory.FiniteMeasure Ω`, the implementation of `MeasureTheory.ProbabilityMeasure Ω`
is directly as a subtype of `MeasureTheory.Measure Ω`, and the coercion to a function is the
composition `ENNReal.toNNReal` and the coercion to function of `MeasureTheory.Measure Ω`.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

convergence in distribution, convergence in law, weak convergence of measures, probability measure

-/

noncomputable section

open Set Filter BoundedContinuousFunction Topology

open scoped ENNReal NNReal

namespace MeasureTheory

section ProbabilityMeasure

/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`MeasureTheory.ProbabilityMeasure Ω`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[OpensMeasurableSpace Ω]`), then `MeasureTheory.ProbabilityMeasure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the mapping
`MeasureTheory.ProbabilityMeasure.toFiniteMeasure`.
-/

def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }

namespace ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

-- INSTANCE (free from Core): [Inhabited
