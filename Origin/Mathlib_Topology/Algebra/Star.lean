/-
Extracted from Topology/Algebra/Star.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuity of `star`

This file defines the `ContinuousStar` typeclass, along with instances on `Pi`, `Prod`,
`MulOpposite`, and `Units`.
-/

open Filter Topology

class ContinuousStar (R : Type*) [TopologicalSpace R] [Star R] : Prop where
  /-- The `star` operator is continuous. -/
  continuous_star : Continuous (star : R → R)

export ContinuousStar (continuous_star)

section Continuity

variable {α R : Type*} [TopologicalSpace R] [Star R] [ContinuousStar R]

theorem continuousOn_star {s : Set R} : ContinuousOn star s :=
  continuous_star.continuousOn

theorem continuousWithinAt_star {s : Set R} {x : R} : ContinuousWithinAt star s x :=
  continuous_star.continuousWithinAt

theorem continuousAt_star {x : R} : ContinuousAt star x :=
  continuous_star.continuousAt

theorem tendsto_star (a : R) : Tendsto star (𝓝 a) (𝓝 (star a)) :=
  continuousAt_star

theorem Filter.Tendsto.star {f : α → R} {l : Filter α} {y : R} (h : Tendsto f l (𝓝 y)) :
    Tendsto (fun x => star (f x)) l (𝓝 (star y)) :=
  (continuous_star.tendsto y).comp h

variable [TopologicalSpace α] {f : α → R} {s : Set α} {x : α}
