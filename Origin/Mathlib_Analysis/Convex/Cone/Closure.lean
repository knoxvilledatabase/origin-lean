/-
Extracted from Analysis/Convex/Cone/Closure.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Closure of cones

We define the closures of convex and pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

namespace ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]

variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ ↦ K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem
