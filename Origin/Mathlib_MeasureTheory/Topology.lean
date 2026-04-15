/-
Extracted from MeasureTheory/Topology.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Theorems combining measure theory and topology

This file gathers theorems that combine measure theory and topology, and cannot easily be added to
the existing files without introducing massive dependencies between the subjects.
-/

open Filter MeasureTheory

theorem ae_restrict_le_codiscreteWithin
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α]
    {μ : Measure α} [NoAtoms μ] {U : Set α} (hU : MeasurableSet U) :
    ae (μ.restrict U) ≤ codiscreteWithin U := by
  intro s hs
  have : DiscreteTopology ↑(sᶜ ∩ U) := isDiscrete_iff_discreteTopology.mp
    <| isDiscrete_of_codiscreteWithin ((compl_compl s).symm ▸ hs)
  rw [mem_ae_iff, Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)
