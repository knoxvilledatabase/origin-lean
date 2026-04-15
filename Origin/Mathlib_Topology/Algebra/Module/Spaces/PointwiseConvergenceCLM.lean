/-
Extracted from Topology/Algebra/Module/Spaces/PointwiseConvergenceCLM.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology of pointwise convergence on continuous linear maps

## Main definitions

* `PointwiseConvergenceCLM`: Type synonym of `E →SL[σ] F` equipped with the uniform convergence
  topology on finite sets.
* `PointwiseConvergenceCLM.evalCLM`: The evaluation map `(f : E →SLₚₜ[σ] F) ↦ f a` for fixed `a : E`
  as a continuous linear map.
* `ContinuousLinearMap.toPointwiseConvergenceCLM`: The canonical map from `E →SL[σ] F` to
  `E →SLₚₜ[σ] F` as a continuous linear map. This is the statement that bounded convergence is
  stronger than pointwise convergence.
* `PointwiseConvergenceCLM.equivWeakDual`: The continuous equivalence between `E →Lₚₜ[𝕜] 𝕜` and
  `WeakDual 𝕜 E`.

## Main statements

* `PointwiseConvergenceCLM.tendsto_iff_forall_tendsto`: In the topology of pointwise convergence,
  `a` converges to `a₀` iff for every `x : E` the map `a · x` converges to `a₀ x`.
* `PointwiseConvergenceCLM.continuous_of_continuous_eval`: A map to `g : α → E →SLₚₜ[σ] F` is
  continuous if for every `x : E` the evaluation `g · x` is continuous.

## Notation

* `E →SLₚₜ[σ] F` is space of continuous linear maps equipped with pointwise convergence topology.

-/

/-! ### Topology of pointwise convergence -/

variable {α ι : Type*} [TopologicalSpace α]

variable {𝕜 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜] [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]

variable {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ]

variable {E F Fᵤ G : Type*} [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup Fᵤ] [UniformSpace Fᵤ] [IsUniformAddGroup Fᵤ]
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 Fᵤ] [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₂ Fᵤ] [Module 𝕜₃ G]

open Set Topology

variable (σ E F) in

abbrev PointwiseConvergenceCLM := UniformConvergenceCLM σ F {s : Set E | Finite s}
