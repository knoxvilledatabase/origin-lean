/-
Extracted from MeasureTheory/Measure/Typeclasses/NoAtoms.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Measures having no atoms

A measure `μ` has no atoms if the measure of each singleton is zero.

## TODO

Should `NoAtoms` be redefined as `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`?
-/

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

class NoAtoms {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0

export MeasureTheory.NoAtoms (measure_singleton)

attribute [simp] measure_singleton

variable [NoAtoms μ]

theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton

theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, Measure.restrict_eq_zero]

-- INSTANCE (free from Core): Measure.restrict.instNoAtoms

theorem _root_.Set.Countable.measure_zero (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ s = 0 := by
  rw [← biUnion_of_singleton s, measure_biUnion_null_iff h]
  simp

theorem _root_.Set.Countable.ae_notMem (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    ∀ᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using h.measure_zero μ

lemma Measure.ae_ne (μ : Measure α) [NoAtoms μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=
  (countable_singleton a).ae_notMem μ

lemma _root_.Set.Countable.measure_restrict_compl (h : s.Countable) (μ : Measure α) [NoAtoms μ] :
    μ.restrict sᶜ = μ :=
  restrict_eq_self_of_ae_mem <| h.ae_notMem μ
