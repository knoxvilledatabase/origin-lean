/-
Extracted from Topology/Algebra/Module/Spaces/ContinuousLinearMap.lean
Genuine: 13 of 23 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Topology of bounded convergence on the space of continuous linear map

In this file, we endow `E →L[𝕜] F` with the "topology of bounded convergence",
or "topology of uniform convergence on bounded sets". This is declared as an instance.

A key feature of the topology of bounded convergence is that, in the normed setting, it coincides
with the operator norm topology.

Note that, more generally, we defined the "topology of `𝔖`-convergence" for any
`𝔖 : Set (Set E)` in `Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## Main definitions

* `ContinuousLinearMap.topologicalSpace` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `ContinuousLinearMap.topologicalAddGroup` and
  `ContinuousLinearMap.continuousSMul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

open Bornology Filter Function Set Topology

open scoped UniformConvergence Uniformity

namespace ContinuousLinearMap

section BoundedConvergence

/-! ### Topology of bounded convergence  -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

-- INSTANCE (free from Core): topologicalSpace

-- INSTANCE (free from Core): topologicalAddGroup

-- INSTANCE (free from Core): continuousSMul

-- INSTANCE (free from Core): uniformSpace

-- INSTANCE (free from Core): isUniformAddGroup

-- INSTANCE (free from Core): instContinuousEvalConst

-- INSTANCE (free from Core): instT2Space

protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

theorem isUniformEmbedding_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformEmbedding
      fun f : E →SL[σ] F ↦ UniformOnFun.ofFun {s | Bornology.IsVonNBounded 𝕜₁ s} f :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn ..

-- INSTANCE (free from Core): uniformContinuousConstSMul

-- INSTANCE (free from Core): continuousConstSMul

protected theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (i : ι) (_ : p i),
        𝓟 {f : E →SL[σ] F | MapsTo f s (b i)} :=
  UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h

protected theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (U : Set F) (_ : U ∈ 𝓝 0),
        𝓟 {f : E →SL[σ] F | MapsTo f s U} :=
  UniformConvergenceCLM.nhds_zero_eq ..

theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SL[σ] F in 𝓝 0, MapsTo f s U :=
  UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} (hS : IsVonNBounded R S) {s : Set E} (hs : IsVonNBounded 𝕜₁ s) :
    IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} :
    IsVonNBounded R S ↔
      ∀ s, IsVonNBounded 𝕜₁ s → IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_iff

theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    [ContinuousSMul 𝕜₁ E] (h : IsCoherentWith {s : Set E | IsVonNBounded 𝕜₁ s}) :
    CompleteSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ

-- INSTANCE (free from Core): instCompleteSpace

theorem isUniformInducing_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformInducing f) :
    IsUniformInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _

theorem isUniformEmbedding_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

variable [TopologicalSpace F] [TopologicalSpace G] (𝔖 : Set (Set E)) (𝔗 : Set (Set F))

theorem isInducing_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsInducing f) :
    IsInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp f <| AddMonoidHom.isUniformInducing_of_isInducing hf).isInducing

theorem isEmbedding_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsEmbedding f) :
    IsEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  .mk (isInducing_postcomp f hf.isInducing) fun _ _ ↦ f.cancel_left hf.injective

variable (G) in
