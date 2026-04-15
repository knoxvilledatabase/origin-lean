/-
Extracted from Topology/Algebra/Module/Spaces/CompactConvergenceCLM.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Topology of compact convergence on the space of continuous linear maps

In this file, we define a type alias `CompactConvergenceCLM` for `E →L[𝕜] F`,
endowed with the topology of uniform convergence on compact subsets.

More concretely, `CompactConvergenceCLM` is an abbreviation for
`UniformConvergenceCLM σ F {(S : Set E) | IsCompact S}`. We denote it by `E →SL_c[σ] F`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

open Bornology Filter Function Set Topology ContinuousLinearMap

open scoped UniformConvergence Uniformity

section CompactSets

/-! ### Topology of compact convergence for continuous linear maps -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*}
  [AddCommGroup E] [Module 𝕜₁ E]
  [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G]

variable (E F σ) in

abbrev CompactConvergenceCLM [TopologicalSpace E] [TopologicalSpace F] :=
  UniformConvergenceCLM σ F {(S : Set E) | IsCompact S}
