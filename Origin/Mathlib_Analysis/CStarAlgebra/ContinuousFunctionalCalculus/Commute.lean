/-
Extracted from Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Commuting with applications of the continuous functional calculus

This file shows that if an element `b` commutes with both `a` and `star a`, then it commutes
with `cfc f a` (or `cfcₙ f a`). In the case where `a` is selfadjoint, we may reduce the hypotheses.

## Main results

* `Commute.cfc` and `Commute.cfcₙ`: an element commutes with `cfc f a` or `cfcₙ f a` if it
  commutes with both `a` and `star a`. Specialized versions for `ℝ` and `ℝ≥0` or for
  `IsSelfAdjoint a` which do not require the user to show the element commutes with `star a` are
  provided for convenience.

## Implementation notes

The proof of `Commute.cfcHom` and `Commute.cfcₙHom` could be made simpler by appealing to basic
facts about double commutants, but doing so would require extra type class assumptions so that we
can talk about topological star algebras. Instead, we avoid this to minimize the work Lean must do
to call these lemmas, and give a straightforward proof by induction.

-/

variable {𝕜 A : Type*}

open scoped NNReal

section Unital

section RCLike

variable {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]

variable [TopologicalSpace A] [ContinuousFunctionalCalculus 𝕜 A p]
  [IsSemitopologicalRing A] [T2Space A]

open StarAlgebra.elemental in

protected theorem Commute.cfcHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b := by
  open scoped ContinuousFunctionalCalculus in
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    conv =>
      enter [1, 2]
      equals algebraMap 𝕜 _ r => rfl
    rw [AlgHomClass.commutes]
    exact Algebra.commute_algebraMap_left r b
  | id => rwa [cfcHom_id ha]
  | star_id => rwa [map_star, cfcHom_id]
  | add f g hf hg => rw [map_add]; exact hf.add_left hg
  | mul f g hf hg => rw [map_mul]; exact mul_left hf hg
  | frequently f hf =>
    rw [commute_iff_eq, ← Set.mem_setOf (p := fun x => x * b = b * x),
      ← (isClosed_eq (by fun_prop) (by fun_prop)).closure_eq]
    apply mem_closure_of_frequently_of_tendsto hf
    exact cfcHom_continuous ha |>.tendsto _

protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  hb.cfcHom ha (ha'.star_eq.symm ▸ hb) f
