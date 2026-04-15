/-
Extracted from Topology/Algebra/Module/Alternating/Topology.lean
Genuine: 9 of 16 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-!
# Topology on continuous alternating maps

In this file we define `UniformSpace` and `TopologicalSpace` structures
on the space of continuous alternating maps between topological vector spaces.

The structures are induced by those on `ContinuousMultilinearMap`s,
and most of the lemmas follow from the corresponding lemmas about `ContinuousMultilinearMap`s.
-/

open Bornology Function Set Topology

open scoped UniformConvergence Filter

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

section IsClosedRange

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

-- INSTANCE (free from Core): instTopologicalSpace

lemma isClosed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] :
    IsClosed (Set.range (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)) := by
  simp only [range_toContinuousMultilinearMap, setOf_forall]
  repeat refine isClosed_iInter fun _ ↦ ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

end IsClosedRange

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

-- INSTANCE (free from Core): instUniformSpace

lemma uniformContinuous_toContinuousMultilinearMap :
    UniformContinuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous

theorem uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] :
    UniformContinuous (DFunLike.coe : (E [⋀^ι]→L[𝕜] F) → (ι → E) → F) :=
  ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

theorem uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι → E) :
    UniformContinuous fun f : E [⋀^ι]→L[𝕜] F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

-- INSTANCE (free from Core): instIsUniformAddGroup

-- INSTANCE (free from Core): instUniformContinuousConstSMul

theorem isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [Module 𝕜 G] (g : F →L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousAlternatingMap : (E [⋀^ι]→L[𝕜] F) → (E [⋀^ι]→L[𝕜] G)) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

section CompleteSpace

variable [ContinuousSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in

theorem completeSpace (h : IsCoherentWith {s : Set (ι → E) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) := by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousAlternatingMap f
      ext
      simp
  have := ContinuousMultilinearMap.completeSpace (F := F) h
  rw [completeSpace_iff_isComplete_range
    isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing]
  apply isClosed_range_toContinuousMultilinearMap.isComplete

-- INSTANCE (free from Core): instCompleteSpace

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F] [ContinuousSMul 𝕜 E]

theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap

theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

lemma isEmbedding_toContinuousMultilinearMap :
    IsEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding

-- INSTANCE (free from Core): instIsTopologicalAddGroup
