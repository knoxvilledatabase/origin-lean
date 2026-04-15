/-
Extracted from Topology/MetricSpace/UniformConvergence.lean
Genuine: 14 of 22 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-! # Metric structure on `α →ᵤ β` and `α →ᵤ[𝔖] β` for finite `𝔖`

When `β` is a (pseudo, extended) metric space it is a uniform space, and therefore we may
consider the type `α →ᵤ β` of functions equipped with the topology of uniform convergence. The
natural (pseudo, extended) metric on this space is given by `fun f g ↦ ⨆ x, edist (f x) (g x)`,
and this induces the existing uniformity. Unless `β` is a bounded space, this will not be a (pseudo)
metric space (except in the trivial case where `α` is empty).

When `𝔖 : Set (Set α)` is a collection of subsets, we may equip the space of functions with the
(pseudo, extended) metric `fun f g ↦ ⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)`. *However*, this only induces
the pre-existing uniformity on `α →ᵤ[𝔖] β` if `𝔖` is finite, and hence we only have an instance in
that case. Nevertheless, this still covers the most important case, such as when `𝔖` is a singleton.

Furthermore, we note that this is essentially a mathematical obstruction, not a technical one:
indeed, the uniformity of `α →ᵤ[𝔖] β` is countably generated only when there is a sequence
`t : ℕ → Finset (Set α)` such that, for each `n`, `t n ⊆ 𝔖`, `fun n ↦ Finset.sup (t n)` is monotone
and for every `s ∈ 𝔖`, there is some `n` such that `s ⊆ Finset.sup (t n)` (see
`UniformOnFun.isCountablyGenerated_uniformity`). So, while the `𝔖` for which `α →ᵤ[𝔖] β` is
metrizable include some non-finite `𝔖`, there are some `𝔖` which are not metrizable, and moreover,
it is only when `𝔖` is finite that `⨆ x ∈ ⋃₀ 𝔖, edist (f x) (g x)` is a metric which induces the
uniformity.

There are a few advantages of equipping this space with this metric structure.

1. A function `f : X → α →ᵤ β` is Lipschitz in this metric if and only if for every `a : α` it is
  Lipschitz in the first variable with the same Lipschitz constant.
2. It provides a natural setting in which one can talk about the metrics on `α →ᵇ β` or, when
  `α` is compact, `C(α, β)`, relative to their underlying bare functions.
-/

variable {α β γ : Type*} [PseudoEMetricSpace γ]

open scoped UniformConvergence NNReal ENNReal

open Filter Topology Uniformity

namespace UniformFun

section EMetric

variable [PseudoEMetricSpace β]

-- INSTANCE (free from Core): :

lemma edist_le {f g : α →ᵤ β} {C : ℝ≥0∞} :
    edist f g ≤ C ↔ ∀ x, edist (toFun f x) (toFun g x) ≤ C :=
  iSup_le_iff

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): {β

lemma lipschitzWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ c, LipschitzWith K (fun x ↦ toFun (f x) c) := by
  simp [LipschitzWith, edist_le, forall_comm (α := α)]

lemma lipschitzWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} :
    LipschitzWith K (fun x ↦ ofFun (f x)) ↔ ∀ c, LipschitzWith K (f · c) :=
  lipschitzWith_iff

lemma _root_.LipschitzWith.uniformEquicontinuous (f : α → γ → β) (K : ℝ≥0)
    (h : ∀ c, LipschitzWith K (f c)) : UniformEquicontinuous f := by
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [← lipschitzWith_ofFun_iff] at h
  exact h.uniformContinuous

lemma lipschitzOnWith_iff {f : γ → α →ᵤ β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K f s ↔ ∀ c, LipschitzOnWith K (fun x ↦ toFun (f x) c) s := by
  simp [lipschitzOnWith_iff_restrict, lipschitzWith_iff]
  rfl

lemma lipschitzOnWith_ofFun_iff {f : γ → α → β} {K : ℝ≥0} {s : Set γ} :
    LipschitzOnWith K (fun x ↦ ofFun (f x)) s ↔ ∀ c, LipschitzOnWith K (f · c) s :=
  lipschitzOnWith_iff

lemma _root_.LipschitzOnWith.uniformEquicontinuousOn (f : α → γ → β) (K : ℝ≥0) {s : Set γ}
    (h : ∀ c, LipschitzOnWith K (f c) s) : UniformEquicontinuousOn f s := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn]
  rw [← lipschitzOnWith_ofFun_iff] at h
  exact h.uniformContinuousOn

lemma edist_eval_le {f g : α →ᵤ β} {x : α} :
    edist (toFun f x) (toFun g x) ≤ edist f g :=
  edist_le.mp le_rfl x

lemma lipschitzWith_eval (x : α) :
    LipschitzWith 1 (fun f : α →ᵤ β ↦ toFun f x) := by
  intro f g
  simpa using edist_eval_le

end EMetric

section Metric

variable [PseudoMetricSpace β]

-- INSTANCE (free from Core): [BoundedSpace

lemma dist_le [BoundedSpace β] {f g : α →ᵤ β} {C : ℝ} (hC : 0 ≤ C) :
    dist f g ≤ C ↔ ∀ x, dist (toFun f x) (toFun g x) ≤ C := by
  simp_rw [dist_edist, ← ENNReal.le_ofReal_iff_toReal_le (edist_ne_top _ _) hC, edist_le]

-- INSTANCE (free from Core): [BoundedSpace

-- INSTANCE (free from Core): {β

open BoundedContinuousFunction in

lemma isometry_ofFun_boundedContinuousFunction [TopologicalSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : (α →ᵇ β) → α →ᵤ β) := by
  simp [Isometry, edist_def, edist_eq_iSup]

lemma isometry_ofFun_continuousMap [TopologicalSpace α] [CompactSpace α] :
    Isometry (ofFun ∘ DFunLike.coe : C(α, β) → α →ᵤ β) :=
  isometry_ofFun_boundedContinuousFunction.comp <|
    ContinuousMap.isometryEquivBoundedOfCompact α β |>.isometry

lemma edist_continuousMapMk [TopologicalSpace α] [CompactSpace α]
    {f g : α →ᵤ β} (hf : Continuous (toFun f)) (hg : Continuous (toFun g)) :
    edist (⟨_, hf⟩ : C(α, β)) ⟨_, hg⟩ = edist f g := by
  simp [← isometry_ofFun_continuousMap.edist_eq]

end Metric

end UniformFun

namespace UniformOnFun

variable {𝔖 𝔗 : Set (Set α)}

section EMetric

variable [PseudoEMetricSpace β]

lemma continuous_of_forall_lipschitzWith {f : γ → α →ᵤ[𝔖] β} (K : Set α → ℝ≥0)
    (h : ∀ s ∈ 𝔖, ∀ c ∈ s, LipschitzWith (K s) (fun x ↦ toFun 𝔖 (f x) c)) :
    Continuous f := by
  rw [UniformOnFun.continuous_rng_iff]
  refine fun s hs ↦ LipschitzWith.continuous (K := K s) ?_
  rw [UniformFun.lipschitzWith_iff]
  rintro ⟨y, hy⟩
  exact h s hs y hy
