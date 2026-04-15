/-
Extracted from Topology/VectorBundle/Constructions.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Standard constructions on vector bundles

This file contains several standard constructions on vector bundles:

* `Bundle.Trivial.vectorBundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `VectorBundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `fun x ↦ E₁ x × E₂ x`).

* `VectorBundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/

noncomputable section

open Bundle Set FiberBundle

/-! ### The trivial vector bundle -/

namespace Bundle.Trivial

variable (𝕜 : Type*) (B : Type*) (F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace B]

-- INSTANCE (free from Core): trivialization.isLinear

variable {𝕜} in

theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]

-- INSTANCE (free from Core): vectorBundle
