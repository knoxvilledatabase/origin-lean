/-
Extracted from Analysis/Calculus/TangentCone/DimOne.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Unique differentiability property of a set in the base field

In this file we prove that a set in the base field has the unique differentiability property at `x`
iff `x` is an accumulation point of the set, see `uniqueDiffWithinAt_iff_accPt`.
-/

open Filter Metric Set

open scoped Topology

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

theorem tangentConeAt_eq_univ {s : Set 𝕜} {x : 𝕜} (hx : AccPt x (𝓟 s)) :
    tangentConeAt 𝕜 s x = univ := by
  refine eq_univ_of_forall fun y ↦ ?_
  apply mem_tangentConeAt_of_frequently (𝓝[≠] x) (fun z ↦ y / (z - x)) (· - x)
  · exact Continuous.tendsto' (by fun_prop) _ _ (by simp) |>.mono_left inf_le_left
  · simpa [accPt_iff_frequently_nhdsNE] using hx
  · apply tendsto_nhds_of_eventually_eq
    refine eventually_mem_nhdsWithin.mono fun z hz ↦ ?_
    have : z - x ≠ 0 := by simpa [sub_eq_zero] using hz
    simp [div_mul_cancel₀ _ this]

theorem uniqueDiffWithinAt_iff_accPt {s : Set 𝕜} {x : 𝕜} :
    UniqueDiffWithinAt 𝕜 s x ↔ AccPt x (𝓟 s) :=
  ⟨UniqueDiffWithinAt.accPt, fun h ↦
    ⟨by simp [tangentConeAt_eq_univ h], mem_closure_iff_clusterPt.mpr h.clusterPt⟩⟩

alias ⟨_, AccPt.uniqueDiffWithinAt⟩ := uniqueDiffWithinAt_iff_accPt
