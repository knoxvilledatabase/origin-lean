/-
Extracted from Analysis/Calculus/TangentCone/Defs.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Tangent cone

In this file, we define two predicates `UniqueDiffWithinAt 𝕜 s x` and `UniqueDiffOn 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangentConeAt`,
and express `UniqueDiffWithinAt` and `UniqueDiffOn` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `UniqueDiffWithinAt` and `UniqueDiffOn` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`. Hence, derivatives
are not defined yet. The property of uniqueness of the derivative is therefore proved in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`, but based on the properties of the tangent cone we
prove here.
-/

open Filter Set Metric

open scoped Topology Pointwise

universe u v

variable (R : Type u) {E : Type v}

section TangentConeAt

variable [AddCommGroup E] [SMul R E] [TopologicalSpace E] {s : Set E} {x y : E}

irreducible_def tangentConeAt (s : Set E) (x : E) : Set E :=
  {y : E | ClusterPt y ((⊤ : Filter R) • 𝓝[(x + ·) ⁻¹' s] 0)}

variable {R}

theorem mem_tangentConeAt_of_frequently {α : Type*} (l : Filter α) (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∃ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x := by
  suffices Tendsto (fun n ↦ c n • d n) (l ⊓ 𝓟 {y | x + d y ∈ s}) (⊤ • 𝓝[(x + ·) ⁻¹' s] 0) by
    rw [frequently_iff_neBot] at hds
    rw [tangentConeAt_def]
    exact ClusterPt.mono (hcd.mono_left inf_le_left).mapClusterPt this
  rw [← map₂_smul, ← map_prod_eq_map₂]
  refine tendsto_map.comp (tendsto_top.prodMk (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩))
  · exact hd₀.mono_left inf_le_left
  · simp [eventually_inf_principal]

theorem mem_tangentConeAt_of_seq {α : Type*} (l : Filter α) [l.NeBot] (c : α → R) (d : α → E)
    (hd₀ : Tendsto d l (𝓝 0)) (hds : ∀ᶠ n in l, x + d n ∈ s)
    (hcd : Tendsto (fun n ↦ c n • d n) l (𝓝 y)) : y ∈ tangentConeAt R s x :=
  mem_tangentConeAt_of_frequently l c d hd₀ hds.frequently hcd

theorem exists_fun_of_mem_tangentConeAt (h : y ∈ tangentConeAt R s x) :
    ∃ (α : Type (max u v)) (l : Filter α) (_hl : l.NeBot) (c : α → R) (d : α → E),
      Tendsto d l (𝓝 0) ∧ (∀ᶠ n in l, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) l (𝓝 y) := by
  rw [tangentConeAt, mem_setOf, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
    ← neBot_inf_comap_iff_map'] at h
  refine ⟨R × E, _, h, Prod.fst, Prod.snd, ?_, ?_, ?_⟩
  · refine (tendsto_snd (f := ⊤)).mono_left <| inf_le_right.trans <| ?_
    gcongr
    apply nhdsWithin_le_nhds
  · refine .filter_mono inf_le_right ?_
    rw [top_prod, eventually_comap]
    filter_upwards [eventually_mem_nhdsWithin]
    simp +contextual
  · exact tendsto_comap.mono_left inf_le_left

end TangentConeAt

abbrev posTangentConeAt [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (s : Set E) (x : E) :
    Set E :=
  tangentConeAt NNReal s x

variable [Semiring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
