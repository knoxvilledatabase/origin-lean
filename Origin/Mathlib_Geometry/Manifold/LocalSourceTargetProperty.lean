/-
Extracted from Geometry/Manifold/LocalSourceTargetProperty.lean
Genuine: 11 of 18 | Dissolved: 0 | Infrastructure: 7
-/
import Origin.Core

/-! # Local properties of smooth functions which depend on both the source and target

In this file, we consider local properties of functions between manifolds, which depend on both the
source and the target: more precisely, properties `P` of functions `f : M → N` such that
`f` has property `P` if and only if there is a suitable pair of charts on `M` and `N`, respectively,
such that `f` read in these charts has a particular form.
The motivating examples of this general description are immersions and submersions:
`f : M → N` is an immersion at `x` iff there are charts `φ` and `ψ` of `M` and `N` around `x` and
`f x`, respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`. Similarly, `f` is a
submersion at `x` iff it looks like a projection `(u, v) ↦ u` in suitable charts near `x` and `f x`.

Studying such local properties allows proving several lemmas about immersions and submersions
only once. In `IsImmersionEmbedding.lean`, we prove that being an immersion at `x` is indeed a
local property of this form.

## Main definitions and results

* `Manifold.LocalSourceTargetPropertyAt` captures a local property of the above form:
  for each `f : M → N`, and pair of charts `φ` of `M` and `ψ` of `N`, the local property is either
  satisfied or not.
  We ask that the property be stable under congruence and under restriction of `φ`.
* `Manifold.LiftSourceTargetPropertyAt f x P`, where `P` is a `LocalSourceTargetPropertyAt`,
  defines a local property of functions of the above shape:
  `f` has this property at `x` if there exist charts `φ` and `ψ` such that `P f φ ψ` holds.
* `Manifold.LiftSourceTargetPropertyAt.congr_of_eventuallyEq`: if `f` has property `P` at `x`
  and `g` equals `f` near `x`, then `g` also has property `P` at `x`.
* `IsOpen.liftSourceTargetPropertyAt`: the set of points at which `LiftSourceTargetPropertyAt`
  holds is open

-/

open scoped Manifold Topology ContDiff

open Function Set

variable {𝕜 E E' F F' H H' G G' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M M' N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

namespace Manifold

structure IsLocalSourceTargetProperty
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop where
  mono_source : ∀ {f : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    ∀ {s : Set M}, IsOpen s → P f φ ψ → P f (φ.restr s) ψ
  -- Note: the analogous `mono_target` statement is true for both immersions and submersions.
  -- If and when a future lemma requires it, add this here.
  congr : ∀ {f g : M → N}, ∀ {φ : OpenPartialHomeomorph M H}, ∀ {ψ : OpenPartialHomeomorph N G},
    EqOn f g φ.source → P f φ ψ → P g φ ψ

variable (I J n) in

structure LocalPresentationAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) where
  /-- A choice of chart on the domain `M` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `codChart`, `f` has the local property `P` at `x`. -/
  domChart : OpenPartialHomeomorph M H
  /-- A choice of chart on the target `N` of the local property `P` of `f` at `x`:
  w.r.t. this chart and `domChart`, `f` has the local property `P` at `x`. -/
  codChart : OpenPartialHomeomorph N G
  mem_domChart_source : x ∈ domChart.source
  mem_codChart_source : f x ∈ codChart.source
  domChart_mem_maximalAtlas : domChart ∈ IsManifold.maximalAtlas I n M
  codChart_mem_maximalAtlas : codChart ∈ IsManifold.maximalAtlas J n N
  source_subset_preimage_source : domChart.source ⊆ f ⁻¹' codChart.source
  property : P f domChart codChart

variable (I J n) in

def LiftSourceTargetPropertyAt (f : M → N) (x : M)
    (P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop) : Prop :=
  Nonempty (LocalPresentationAt I J n f x P)

namespace LiftSourceTargetPropertyAt

variable {f g : M → N} {x : M}
  {P : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop}

noncomputable def localPresentationAt (h : LiftSourceTargetPropertyAt I J n f x P) :
    LocalPresentationAt I J n f x P :=
  Classical.choice h

noncomputable def domChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph M H :=
  h.localPresentationAt.domChart

noncomputable def codChart (h : LiftSourceTargetPropertyAt I J n f x P) :
    OpenPartialHomeomorph N G :=
  h.localPresentationAt.codChart

omit [ChartedSpace H M] [ChartedSpace G N] in

lemma congr_iff (hP : IsLocalSourceTargetProperty P) {f g : M → N}
    {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G} (hfg : EqOn f g φ.source) :
    P f φ ψ ↔ P g φ ψ :=
  ⟨hP.congr hfg, hP.congr hfg.symm⟩

lemma mk_of_continuousAt (hf : ContinuousAt f x)
    (hP : IsLocalSourceTargetProperty P)
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hfP : P f domChart codChart) : LiftSourceTargetPropertyAt I J n f x P := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.preimage_mem_nhds (codChart.open_source.mem_nhds hfx)
  exact ⟨domChart.restr s, codChart, by grind, hfx,
    restr_mem_maximalAtlas (contDiffGroupoid n I) hdomChart hsopen, hcodChart, by grind,
    hP.mono_source hsopen hfP⟩

lemma congr_iff_of_eventuallyEq (hP : IsLocalSourceTargetProperty P) (h' : f =ᶠ[nhds x] g) :
    LiftSourceTargetPropertyAt I J n f x P ↔ LiftSourceTargetPropertyAt I J n g x P :=
  ⟨fun hf ↦ hf.congr_of_eventuallyEq hP h', fun hg ↦ hg.congr_of_eventuallyEq hP h'.symm⟩

lemma _root_.IsOpen.liftSourceTargetPropertyAt :
    IsOpen {x | LiftSourceTargetPropertyAt I J n g x P} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  -- Suppose the lifted property `P` holds at `x`:
  -- choose slice charts `φ` near `x` and `ψ` near `f x` s.t. `P f φ ψ` holds.
  -- Then the same charts witness that `P f φ ψ` holds at any `y ∈ φ.source`.
  refine ⟨hx.domChart.source, fun y hy ↦ ?_, hx.domChart.open_source, hx.mem_domChart_source⟩
  exact ⟨hx.domChart, hx.codChart, hy, hx.source_subset_preimage_source hy,
    hx.domChart_mem_maximalAtlas, hx.codChart_mem_maximalAtlas, hx.source_subset_preimage_source,
    hx.property⟩

lemma prodMap [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    {Q : (M' → N') → OpenPartialHomeomorph M' H' → OpenPartialHomeomorph N' G' → Prop}
    {R : ((M × M') → (N × N')) → OpenPartialHomeomorph (M × M') (H × H') →
      OpenPartialHomeomorph (N × N') (G × G') → Prop}
    (hf : LiftSourceTargetPropertyAt I J n f x P) {g : M' → N'} {x' : M'}
    (hg : LiftSourceTargetPropertyAt I' J' n g x' Q)
    (h : ∀ {f : M → N}, ∀ {φ₁ : OpenPartialHomeomorph M H}, ∀ {ψ₁ : OpenPartialHomeomorph N G},
      ∀ {g : M' → N'}, ∀ {φ₂ : OpenPartialHomeomorph M' H'}, ∀ {ψ₂ : OpenPartialHomeomorph N' G'},
      P f φ₁ ψ₁ → Q g φ₂ ψ₂ → R (Prod.map f g) (φ₁.prod φ₂) (ψ₁.prod ψ₂)) :
    LiftSourceTargetPropertyAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') R := by
  use hf.domChart.prod hg.domChart, hf.codChart.prod hg.codChart
  · simp [hf.mem_domChart_source, hg.mem_domChart_source]
  · simp [mem_codChart_source hf, mem_codChart_source hg]
  · exact IsManifold.mem_maximalAtlas_prod
      (domChart_mem_maximalAtlas hf) (domChart_mem_maximalAtlas hg)
  · apply IsManifold.mem_maximalAtlas_prod
      (codChart_mem_maximalAtlas hf) (codChart_mem_maximalAtlas hg)
  · simp only [OpenPartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source,
      preimage_prod_map_prod]
    exact prod_mono hf.source_subset_preimage_source hg.source_subset_preimage_source
  · exact h hf.property hg.property

end LiftSourceTargetPropertyAt

end Manifold
