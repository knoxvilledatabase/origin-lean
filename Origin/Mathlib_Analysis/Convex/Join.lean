/-
Extracted from Analysis/Convex/Join.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex join

This file defines the convex join of two sets. The convex join of `s` and `t` is the union of the
segments with one end in `s` and the other in `t`. This is notably a useful gadget to deal with
convex hulls of finite sets.
-/

open Set

variable {ι : Sort*} {𝕜 E : Type*}

section OrderedSemiring

variable (𝕜) [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  {s t s₁ s₂ t₁ t₂ u : Set E}
  {x y : E}

def convexJoin (s t : Set E) : Set E :=
  ⋃ (x ∈ s) (y ∈ t), segment 𝕜 x y

variable {𝕜}

theorem mem_convexJoin : x ∈ convexJoin 𝕜 s t ↔ ∃ a ∈ s, ∃ b ∈ t, x ∈ segment 𝕜 a b := by
  simp [convexJoin]

theorem convexJoin_comm (s t : Set E) : convexJoin 𝕜 s t = convexJoin 𝕜 t s :=
  (iUnion₂_comm _).trans <| by simp_rw [convexJoin, segment_symm]

theorem convexJoin_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s₁ t₁ ⊆ convexJoin 𝕜 s₂ t₂ :=
  biUnion_mono hs fun _ _ => biUnion_subset_biUnion_left ht

theorem convexJoin_mono_left (hs : s₁ ⊆ s₂) : convexJoin 𝕜 s₁ t ⊆ convexJoin 𝕜 s₂ t :=
  convexJoin_mono hs Subset.rfl

theorem convexJoin_mono_right (ht : t₁ ⊆ t₂) : convexJoin 𝕜 s t₁ ⊆ convexJoin 𝕜 s t₂ :=
  convexJoin_mono Subset.rfl ht
