/-
Extracted from Topology/Algebra/Affine.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topological properties of affine spaces and maps

This file contains a few facts regarding the continuity of affine maps.
-/

namespace AffineMap

variable
  {R V P W Q : Type*}
  [AddCommGroup V] [TopologicalSpace V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup W] [TopologicalSpace W]
  [AddTorsor W Q] [TopologicalSpace Q] [IsTopologicalAddTorsor Q]

section Ring

variable [Ring R] [Module R V] [Module R W]

theorem continuous_linear_iff {f : P →ᵃ[R] Q} : Continuous f.linear ↔ Continuous f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_continuous_iff, Homeomorph.comp_continuous_iff']

theorem isOpenMap_linear_iff {f : P →ᵃ[R] Q} : IsOpenMap f.linear ↔ IsOpenMap f := by
  inhabit P
  have :
    (f.linear : V → W) =
      (Homeomorph.vaddConst <| f default).symm ∘ f ∘ (Homeomorph.vaddConst default) := by
    ext v
    simp
  rw [this]
  simp only [Homeomorph.comp_isOpenMap_iff, Homeomorph.comp_isOpenMap_iff']

variable [TopologicalSpace R] [ContinuousSMul R V]
