/-
Extracted from Topology/Algebra/SeparationQuotient/Section.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Algebraic operations on `SeparationQuotient`

In this file we construct a section of the quotient map `E → SeparationQuotient E` as a continuous
linear map `SeparationQuotient E →L[K] E`.
-/

open Topology

namespace SeparationQuotient

section VectorSpace

variable (K E : Type*) [DivisionRing K] [AddCommGroup E] [Module K E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul K E]

theorem exists_out_continuousLinearMap :
    ∃ f : SeparationQuotient E →L[K] E, mkCLM K E ∘L f = .id K (SeparationQuotient E) := by
  rcases (mkCLM K E).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr surjective_mk) with ⟨f, hf⟩
  replace hf : mk ∘ f = id := congr_arg DFunLike.coe hf
  exact ⟨⟨f, isInducing_mk.continuous_iff.2 (by continuity)⟩, DFunLike.ext' hf⟩

noncomputable def outCLM : SeparationQuotient E →L[K] E :=
  (exists_out_continuousLinearMap K E).choose
