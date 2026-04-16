/-
Extracted from MeasureTheory/MeasurableSpace/NCard.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Set.Card

noncomputable section

/-!
# Measurability of `Set.encard` and `Set.ncard`

In this file we prove that `Set.encard` and `Set.ncard` are measurable functions,
provided that the ambient space is countable.
-/

open Set

variable {α : Type*} [Countable α]

@[measurability]
theorem measurable_encard : Measurable (Set.encard : Set α → ℕ∞) :=
  ENat.measurable_iff.2 fun _n ↦ Countable.measurableSet <| Countable.setOf_finite.mono fun _s hs ↦
    finite_of_encard_eq_coe hs

@[measurability]
theorem measurable_ncard : Measurable (Set.ncard : Set α → ℕ) :=
  Measurable.of_discrete.comp measurable_encard
