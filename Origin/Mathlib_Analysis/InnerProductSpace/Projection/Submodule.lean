/-
Extracted from Analysis/InnerProductSpace/Projection/Submodule.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Subspaces associated with orthogonal projections

Here, the orthogonal projection is used to prove a series of more subtle lemmas about the
orthogonal complement of subspaces of `E` (the orthogonal complement itself was
defined in `Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`) such that they admit
orthogonal projections; the lemma
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`,
stating that for a subspace `K` of `E` such that `K` admits an orthogonal projection we have
`K ⊔ Kᗮ = ⊤`, is a typical example.
-/

variable {𝕜 E F : Type*} [RCLike 𝕜]

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)

namespace Submodule

theorem sup_orthogonal_inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂)
    [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjection K₁ x
  have hvm : x - v ∈ K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

variable {K} in

theorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K ≤ ⊤) using 2
  simp
