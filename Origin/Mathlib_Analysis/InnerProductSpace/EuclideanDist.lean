/-
Extracted from Analysis/InnerProductSpace/EuclideanDist.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Euclidean distance on a finite-dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `toEuclidean` to be
an equivalence between a finite-dimensional topological vector space and the standard Euclidean
space of the same dimension.
Then we define `Euclidean.dist x y = dist (toEuclidean x) (toEuclidean y)` and
provide some definitions (`Euclidean.ball`, `Euclidean.closedBall`) and simple lemmas about this
distance. This way we hide the usage of `toEuclidean` behind an API.
-/

open scoped Topology

open Set

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module ℝ E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]

noncomputable section

open Module

def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

namespace Euclidean

nonrec def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)

def closedBall (x : E) (r : ℝ) : Set E :=
  {y | dist y x ≤ r}

def ball (x : E) (r : ℝ) : Set E :=
  {y | dist y x < r}

theorem ball_subset_closedBall {x : E} {r : ℝ} : ball x r ⊆ closedBall x r := fun _ (hy : _ < r) =>
  le_of_lt hy
