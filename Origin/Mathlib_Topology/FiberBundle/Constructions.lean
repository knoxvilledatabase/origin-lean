/-
Extracted from Topology/FiberBundle/Constructions.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Standard constructions on fiber bundles

This file contains several standard constructions on fiber bundles:

* `Bundle.Trivial.fiberBundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `FiberBundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `fun x ↦ E₁ x × E₂ x`).

* `FiberBundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/

open Bundle Filter Set TopologicalSpace Topology

/-! ### The trivial bundle -/

namespace Bundle

namespace Trivial

variable (B : Type*) (F : Type*)

-- INSTANCE (free from Core): topologicalSpace

variable [TopologicalSpace B] [TopologicalSpace F]

theorem isInducing_toProd : IsInducing (TotalSpace.toProd B F) :=
  ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩
