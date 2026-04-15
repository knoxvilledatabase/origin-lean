/-
Extracted from Analysis/InnerProductSpace/Orthonormal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orthonormal sets

This file defines orthonormal sets in inner product spaces.

## Main results

- We define `Orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.
- Bessel's inequality, `Orthonormal.tsum_inner_products_le`, states that given an orthonormal set
  `v` and a vector `x`, the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more
  than the norm-square of `x`.

For the existence of orthonormal bases, Hilbert bases, etc., see the file
`Analysis.InnerProductSpace.projection`.
-/

noncomputable section

open RCLike Real Filter Module Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section OrthonormalSets_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

variable {𝕜}
