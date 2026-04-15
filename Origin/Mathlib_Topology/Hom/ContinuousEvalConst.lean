/-
Extracted from Topology/Hom/ContinuousEvalConst.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bundled morphisms with continuous evaluation at a point

In this file we define a typeclass
saying that `F` is a type of bundled morphisms (in the sense of `DFunLike`)
with a topology on `F` such that evaluation at a point is continuous in `f : F`.

## Implementation Notes

For now, we define the typeclass for non-dependent bundled functions only.
Whenever we add a type of bundled dependent functions with a topology having this property,
we may decide to generalize from `FunLike` to `DFunLike`.
-/

open scoped Topology

open Filter

class ContinuousEvalConst (F : Type*) (α X : outParam Type*) [FunLike F α X]
    [TopologicalSpace F] [TopologicalSpace X] : Prop where
  continuous_eval_const (x : α) : Continuous fun f : F ↦ f x

export ContinuousEvalConst (continuous_eval_const)

section ContinuousEvalConst

variable {F α X Z : Type*} [FunLike F α X] [TopologicalSpace F] [TopologicalSpace X]
  [ContinuousEvalConst F α X] [TopologicalSpace Z] {f : Z → F} {s : Set Z} {z : Z}

theorem ContinuousEvalConst.of_continuous_forget {F' : Type*} [FunLike F' α X] [TopologicalSpace F']
    {f : F' → F} (hc : Continuous f) (hf : ∀ g, ⇑(f g) = g := by intro; rfl) :
    ContinuousEvalConst F' α X where
  continuous_eval_const x := by simpa only [← hf] using (continuous_eval_const x).comp hc
