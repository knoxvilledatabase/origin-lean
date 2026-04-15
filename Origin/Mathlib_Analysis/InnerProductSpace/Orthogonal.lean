/-
Extracted from Analysis/InnerProductSpace/Orthogonal.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
We make duplicates for `Submodule` and `ClosedSubmodule`.
Some of the more subtle results about the orthogonal complement are delayed to
`Mathlib/Analysis/InnerProductSpace/Projection/`.

See also `BilinForm.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `Submodule.IsOrtho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`Bot`).
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace Submodule

variable (K : Submodule 𝕜 E)

def orthogonal : Submodule 𝕜 E where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right _
  add_mem' hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]
