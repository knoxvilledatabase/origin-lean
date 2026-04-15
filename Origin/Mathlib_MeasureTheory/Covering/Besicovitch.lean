/-
Extracted from MeasureTheory/Covering/Besicovitch.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Besicovitch covering theorems

The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

In this file, we prove the topological Besicovitch covering theorem,
in `Besicovitch.exist_disjoint_covering_families`.

The measurable Besicovitch theorem ensures that, in the same class of metric spaces, if at every
point one considers a class of balls of arbitrarily small radii, called admissible balls, then
one can cover almost all the space by a family of disjoint admissible balls.
It is deduced from the topological Besicovitch theorem, and proved
in `Besicovitch.exists_disjoint_closedBall_covering_ae`.

This implies that balls of small radius form a Vitali family in such spaces. Therefore, theorems
on differentiation of measures hold as a consequence of general results. We restate them in this
context to make them more easily usable.

## Main definitions and results

* `SatelliteConfig α N τ` is the type of all satellite configurations of `N + 1` points
  in the metric space `α`, with parameter `τ`.
* `HasBesicovitchCovering` is a class recording that there exist `N` and `τ > 1` such that
  there is no satellite configuration of `N + 1` points with parameter `τ`.
* `exist_disjoint_covering_families` is the topological Besicovitch covering theorem: from any
  family of balls one can extract finitely many disjoint subfamilies covering the same set.
* `exists_disjoint_closedBall_covering` is the measurable Besicovitch covering theorem: from any
  family of balls with arbitrarily small radii at every point, one can extract countably many
  disjoint balls covering almost all the space. While the value of `N` is relevant for the precise
  statement of the topological Besicovitch theorem, it becomes irrelevant for the measurable one.
  Therefore, this statement is expressed using the `Prop`-valued
  typeclass `HasBesicovitchCovering`.

We also restate the following specialized versions of general theorems on differentiation of
measures:
* `Besicovitch.ae_tendsto_rnDeriv` ensures that `ρ (closedBall x r) / μ (closedBall x r)` tends
  almost surely to the Radon-Nikodym derivative of `ρ` with respect to `μ` at `x`.
* `Besicovitch.ae_tendsto_measure_inter_div` states that almost every point in an arbitrary set `s`
  is a Lebesgue density point, i.e., `μ (s ∩ closedBall x r) / μ (closedBall x r)` tends to `1` as
  `r` tends to `0`. A stronger version for measurable sets is given in
  `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`.

## Implementation

#### Sketch of proof of the topological Besicovitch theorem:

We choose balls in a greedy way. First choose a ball with maximal radius (or rather, since there
is no guarantee the maximal radius is realized, a ball with radius within a factor `τ` of the
supremum). Then, remove all balls whose center is covered by the first ball, and choose among the
remaining ones a ball with radius close to maximum. Go on forever until there is no available
center (this is a transfinite induction in general).

Then define inductively a coloring of the balls. A ball will be of color `i` if it intersects
already chosen balls of color `0`, ..., `i - 1`, but none of color `i`. In this way, balls of the
same color form a disjoint family, and the space is covered by the families of the different colors.

The nontrivial part is to show that at most `N` colors are used. If one needs `N + 1` colors,
consider the first time this happens. Then the corresponding ball intersects `N` balls of the
different colors. Moreover, the inductive construction ensures that the radii of all the balls are
controlled: they form a satellite configuration with `N + 1` balls (essentially by definition of
satellite configurations). Since we assume that there are no such configurations, this is a
contradiction.

#### Sketch of proof of the measurable Besicovitch theorem:

From the topological Besicovitch theorem, one can find a disjoint countable family of balls
covering a proportion `> 1 / (N + 1)` of the space. Taking a large enough finite subset of these
balls, one gets the same property for finitely many balls. Their union is closed. Therefore, any
point in the complement has around it an admissible ball not intersecting these finitely many balls.
Applying again the topological Besicovitch theorem, one extracts from these a disjoint countable
subfamily covering a proportion `> 1 / (N + 1)` of the remaining points, and then even a disjoint
finite subfamily. Then one goes on again and again, covering at each step a positive proportion of
the remaining points, while remaining disjoint from the already chosen balls. The union of all these
balls is the desired almost everywhere covering.
-/

noncomputable section

universe u

open Metric Set Filter Fin MeasureTheory TopologicalSpace

open scoped Topology ENNReal MeasureTheory NNReal

/-!
### Satellite configurations
-/

structure Besicovitch.SatelliteConfig (α : Type*) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  /-- Centers of the balls -/
  c : Fin N.succ → α
  /-- Radii of the balls -/
  r : Fin N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : Pairwise fun i j =>
    r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j
  hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i
  inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N)

namespace Mathlib.Meta.Positivity

open Lean Meta Qq
