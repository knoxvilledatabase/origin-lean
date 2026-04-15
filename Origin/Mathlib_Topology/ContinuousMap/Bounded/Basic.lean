/-
Extracted from Topology/ContinuousMap/Bounded/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bounded continuous functions

The type of bounded continuous functions taking values in a metric space, with the uniform distance.
-/

assert_not_exists CStarRing

noncomputable section

open Topology Bornology NNReal UniformConvergence

open Set Filter Metric Function

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}

structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] : Type max u v extends ContinuousMap α β where
  map_bounded' : ∃ C, ∀ x y, dist (toFun x) (toFun y) ≤ C
