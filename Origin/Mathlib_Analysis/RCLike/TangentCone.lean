/-
Extracted from Analysis/RCLike/TangentCone.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Relationships between unique differentiability over `ℝ` and `ℂ`

A set of unique differentiability for `ℝ` is also a set of unique differentiability for `ℂ`
(or for a general field satisfying `IsRCLikeNormedField 𝕜`).
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [h𝕜 : IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  {s : Set E} {x : E}

theorem tangentConeAt_real_subset_isRCLikeNormedField :
    tangentConeAt ℝ s x ⊆ tangentConeAt 𝕜 s x := by
  letI := h𝕜.rclike
  exact tangentConeAt_mono_field

theorem UniqueDiffWithinAt.of_real (hs : UniqueDiffWithinAt ℝ s x) :
    UniqueDiffWithinAt 𝕜 s x := by
  letI := h𝕜.rclike
  exact hs.mono_field

theorem UniqueDiffOn.of_real (hs : UniqueDiffOn ℝ s) :
    UniqueDiffOn 𝕜 s :=
  fun x hx ↦ (hs x hx).of_real

theorem uniqueDiffWithinAt_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) (hx : x ∈ closure s) :
    UniqueDiffWithinAt 𝕜 s x :=
  UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

theorem uniqueDiffOn_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) : UniqueDiffOn 𝕜 s :=
  UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)
