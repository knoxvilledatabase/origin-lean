/-
Extracted from Topology/ContinuousMap/ZeroAtInfty.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ C₀(α, β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more instances of algebraic structures (e.g., `NonUnitalSemiring`) once the necessary
  type classes (e.g., `IsTopologicalRing`) are sufficiently generalized.
* Relate the unitization of `C₀(α, β)` to the Alexandroff compactification.
-/

universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

structure ZeroAtInftyContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] : Type max u v extends ContinuousMap α β where
  /-- The function tends to zero along the `cocompact` filter. -/
  zero_at_infty' : Tendsto toFun (cocompact α) (𝓝 0)
