/-
Extracted from MeasureTheory/MeasurableSpace/Constructions.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Constructions for measurable spaces and functions

This file provides several ways to construct new measurable spaces and functions from old ones:
`Quotient`, `Subtype`, `Prod`, `Pi`, etc.
-/

assert_not_exists Filter

open Set Function

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y ∈ range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β → α}
    (h : ∀ x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)

set_option backward.isDefEq.respectTransparency false in

theorem ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α → ℕ∞} :
    Measurable f ↔ ∀ n : ℕ, MeasurableSet (f ⁻¹' {↑n}) := by
  refine ⟨fun hf n ↦ hf <| measurableSet_singleton _, fun h ↦ measurable_to_countable' fun n ↦ ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top, ← compl_range_some, preimage_compl, ← iUnion_singleton_eq_range,
      preimage_iUnion]
    exact .compl <| .iUnion h
  | coe n => exact h n
