/-
Extracted from MeasureTheory/OuterMeasure/Caratheodory.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Carathéodory σ-algebra of an outer measure

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `MeasureTheory.OuterMeasure.caratheodory` is the Carathéodory-measurable space
  of an outer measure.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

Carathéodory-measurable, Carathéodory's criterion

-/

noncomputable section

open Set Function Filter

open scoped NNReal Topology ENNReal

namespace MeasureTheory

namespace OuterMeasure

section CaratheodoryMeasurable

universe u

variable {α : Type u} (m : OuterMeasure α)

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable {s s₁ s₂ : Set α}

def IsCaratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s) + m (t \ s)

theorem isCaratheodory_iff_le' {s : Set α} :
    IsCaratheodory m s ↔ ∀ t, m (t ∩ s) + m (t \ s) ≤ m t :=
  forall_congr' fun _ => le_antisymm_iff.trans <| and_iff_right <| measure_le_inter_add_diff _ _ _
