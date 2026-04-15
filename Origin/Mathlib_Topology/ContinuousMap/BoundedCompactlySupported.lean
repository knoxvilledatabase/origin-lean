/-
Extracted from Topology/ContinuousMap/BoundedCompactlySupported.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Compactly supported bounded continuous functions

The two-sided ideal of compactly supported bounded continuous functions taking values in a metric
space, with the uniform distance.
-/

open Set BoundedContinuousFunction

section CompactlySupported

noncomputable def compactlySupported (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing γ] :
    TwoSidedIdeal (α →ᵇ γ) :=
  .mk' {z | HasCompactSupport z} .zero .add .neg .mul_left .mul_right

variable {α γ : Type*} [TopologicalSpace α] [NonUnitalNormedRing γ]
