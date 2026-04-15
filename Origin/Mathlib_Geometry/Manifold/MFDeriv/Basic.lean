/-
Extracted from Geometry/Manifold/MFDeriv/Basic.lean
Genuine: 20 of 21 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basic properties of the manifold Fréchet derivative

In this file, we show various properties of the manifold Fréchet derivative,
mimicking the API for Fréchet derivatives.
- basic properties of unique differentiability sets
- various general lemmas about the manifold Fréchet derivative
- deducing differentiability from smoothness,
- deriving continuity from differentiability on manifolds,
- congruence lemmas for derivatives on manifolds
- composition lemmas and the chain rule

-/

noncomputable section

assert_not_exists tangentBundleCore

open scoped Topology Manifold

open Function Set Bundle ChartedSpace

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

theorem uniqueMDiffWithinAt_univ : UniqueMDiffWithinAt I univ x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

variable {I}

theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffWithinAt I s x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (ht : 𝓝[s] x ≤ 𝓝[t] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds <| by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

theorem UniqueMDiffWithinAt.mono_of_mem_nhdsWithin {s t : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) : UniqueMDiffWithinAt I t x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)

theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffWithinAt I s x) (st : s ⊆ t) :
    UniqueMDiffWithinAt I t x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)

theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)

theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffWithinAt I s x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffWithinAt I (s ∩ t) x :=
  hs.inter' (nhdsWithin_le_nhds ht)

theorem IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueMDiffWithinAt I s x :=
  (uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin <| nhdsWithin_le_nhds <| hs.mem_nhds xs

theorem UniqueMDiffOn.inter (hs : UniqueMDiffOn I s) (ht : IsOpen t) : UniqueMDiffOn I (s ∩ t) :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)

theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiffOn I s :=
  fun _x hx => hs.uniqueMDiffWithinAt hx

theorem uniqueMDiffOn_univ : UniqueMDiffOn I (univ : Set M) :=
  isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s t} (hs : UniqueMDiffWithinAt I s x)
    (ht : UniqueMDiffWithinAt I' t y) : UniqueMDiffWithinAt (I.prod I') (s ×ˢ t) (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod, ← prod_inter_prod]
  rfl

theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiffOn I s)
    (ht : UniqueMDiffOn I' t) : UniqueMDiffOn (I.prod I') (s ×ˢ t) := fun x h ↦
  (hs x.1 h.1).prod (ht x.2 h.2)

theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDifferentiableWithinAt I I' f t x) :
    MDifferentiableWithinAt I I' f s x :=
  ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩

theorem mdifferentiableWithinAt_univ :
    MDifferentiableWithinAt I I' f univ x ↔ MDifferentiableAt I I' f x := by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]

theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]

theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    MDifferentiableWithinAt I I' f (s ∩ t) x ↔ MDifferentiableWithinAt I I' f s x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]

theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDifferentiableAt I I' f x) :
    MDifferentiableWithinAt I I' f s x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDifferentiableWithinAt I I' f s x)
    (hs : s ∈ 𝓝 x) : MDifferentiableAt I I' f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

theorem MDifferentiableOn.mono (h : MDifferentiableOn I I' f t) (st : s ⊆ t) :
    MDifferentiableOn I I' f s := fun x hx => (h x (st hx)).mono st
