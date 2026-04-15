/-
Extracted from Logic/UnivLE.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Logic.Small.Defs

/-!
# UnivLE

A proposition expressing a universe inequality. `UnivLE.{u, v}` expresses that `u ≤ v`,
in the form `∀ α : Type u, Small.{v} α`.

This API indirectly provides an instance for `Small.{u, max u v}`, which could not be declared
directly due to https://github.com/leanprover/lean4/issues/2297.

See the doc-string for the comparison with an alternative stronger definition.
-/

universe u v w

noncomputable section

@[pp_with_univ]
abbrev UnivLE : Prop := ∀ α : Type u, Small.{v} α

example : UnivLE.{u, u} := inferInstance

example : UnivLE.{u, u+1} := inferInstance

example : UnivLE.{0, u} := inferInstance

theorem univLE_max : UnivLE.{u, max u v} := fun α ↦ small_max.{v} α

theorem Small.trans_univLE (α : Type w) [hα : Small.{u} α] [h : UnivLE.{u, v}] :
    Small.{v} α :=
  let ⟨β, ⟨f⟩⟩ := hα.equiv_small
  let ⟨_, ⟨g⟩⟩ := (h β).equiv_small
  ⟨_, ⟨f.trans g⟩⟩

theorem UnivLE.trans [UnivLE.{u, v}] [UnivLE.{v, w}] : UnivLE.{u, w} :=
  fun α ↦ Small.trans_univLE α

instance univLE_of_max [UnivLE.{max u v, v}] : UnivLE.{u, v} := @UnivLE.trans univLE_max ‹_›

example : ¬ UnivLE.{u+1, u} := by
  simp only [small_iff, not_forall, not_exists, not_nonempty_iff]
  exact ⟨Type u, fun α => ⟨fun f => Function.not_surjective_Type.{u, u} f.symm f.symm.surjective⟩⟩
