/-
Extracted from Topology/Covering/Quotient.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covering maps to quotients by free and properly discontinuous group actions
-/

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X)

variable (G : Type*) [Group G] [MulAction G E]

open Topology

structure IsAddQuotientCoveringMap (G) [AddGroup G] [AddAction G E] : Prop
    extends IsQuotientMap f, ContinuousConstVAdd G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ AddAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0
