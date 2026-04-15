/-
Extracted from Topology/Hom/ContinuousEval.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bundled maps with evaluation continuous in both variables

In this file we define a class `ContinuousEval F X Y`
saying that `F` is a bundled morphism class (in the sense of `FunLike`)
with a topology such that `fun (f, x) : F × X ↦ f x` is a continuous function.
-/

open scoped Topology

open Filter

class ContinuousEval (F : Type*) (X Y : outParam Type*) [FunLike F X Y]
    [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] : Prop where
  /-- Evaluation of a bundled morphism at a point is continuous in both variables. -/
  continuous_eval : Continuous fun fx : F × X ↦ fx.1 fx.2

export ContinuousEval (continuous_eval)

variable {F X Y Z : Type*} [FunLike F X Y]
  [TopologicalSpace F] [TopologicalSpace X] [TopologicalSpace Y] [ContinuousEval F X Y]
  [TopologicalSpace Z] {f : Z → F} {g : Z → X} {s : Set Z} {z : Z}
