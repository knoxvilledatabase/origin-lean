/-
Extracted from MeasureTheory/Integral/CompactlySupported.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Integrating compactly supported continuous functions

This file contains definitions and lemmas related to integrals of compactly supported continuous
functions.
-/

open scoped ENNReal NNReal

open CompactlySupported MeasureTheory

variable {X : Type*}

namespace CompactlySupportedContinuousMap

variable [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

lemma integrable {E : Type*} [NormedAddCommGroup E] (f : C_c(X, E))
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

variable [T2Space X] [LocallyCompactSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
