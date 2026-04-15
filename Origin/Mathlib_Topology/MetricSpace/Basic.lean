/-
Extracted from Topology/MetricSpace/Basic.lean
Genuine: 10 of 13 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Basic properties of metric spaces, and instances.

-/

open Set Filter Bornology Topology

open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

variable [PseudoMetricSpace α]

variable {γ : Type w} [MetricSpace γ]

namespace Metric

variable {x : γ} {s : Set γ}

-- INSTANCE (free from Core): (priority

theorem isUniformEmbedding_iff' [PseudoMetricSpace β] {f : γ → β} :
    IsUniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, dist a b < δ → dist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, dist (f a) (f b) < ε → dist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff]

abbrev _root_.MetricSpace.ofT0PseudoMetricSpace (α : Type*) [PseudoMetricSpace α] [T0Space α] :
    MetricSpace α where
  toPseudoMetricSpace := ‹_›
  eq_of_dist_eq_zero hdist := (Metric.inseparable_iff.2 hdist).eq

-- INSTANCE (free from Core): (priority

theorem isClosed_of_pairwise_le_dist {s : Set γ} {ε : ℝ} (hε : 0 < ε)
    (hs : s.Pairwise fun x y => ε ≤ dist x y) : IsClosed s :=
  isClosed_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hs

theorem isClosedEmbedding_of_pairwise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    {ε : ℝ} (hε : 0 < ε) {f : α → γ} (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    IsClosedEmbedding f :=
  isClosedEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

theorem isUniformEmbedding_bot_of_pairwise_le_dist {β : Type*} {ε : ℝ} (hε : 0 < ε) {f : β → α}
    (hf : Pairwise fun x y => ε ≤ dist (f x) (f y)) :
    @IsUniformEmbedding _ _ ⊥ (by infer_instance) f :=
  isUniformEmbedding_of_spaced_out (dist_mem_uniformity hε) <| by simpa using hf

end Metric

abbrev EMetricSpace.toMetricSpaceOfDist {α : Type u} [EMetricSpace α] (dist : α → α → ℝ)
    (dist_nonneg : ∀ x y, 0 ≤ dist x y) (h : ∀ x y, edist x y = .ofReal (dist x y)) :
    MetricSpace α :=
  letI := PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist dist_nonneg h
  MetricSpace.ofT0PseudoMetricSpace _

abbrev EMetricSpace.toMetricSpace {α : Type u} [EMetricSpace α] (h : ∀ x y : α, edist x y ≠ ⊤) :
    MetricSpace α :=
  EMetricSpace.toMetricSpaceOfDist (ENNReal.toReal <| edist · ·) (by simp) (by simp [h])

abbrev MetricSpace.induced {γ β} (f : γ → β) (hf : Function.Injective f) (m : MetricSpace β) :
    MetricSpace γ :=
  { PseudoMetricSpace.induced f m.toPseudoMetricSpace with
    eq_of_dist_eq_zero := fun h => hf (dist_eq_zero.1 h) }

abbrev IsUniformEmbedding.comapMetricSpace {α β} [UniformSpace α] [m : MetricSpace β] (f : α → β)
    (h : IsUniformEmbedding f) : MetricSpace α :=
  .replaceUniformity (.induced f h.injective m) h.comap_uniformity.symm

abbrev Topology.IsEmbedding.comapMetricSpace {α β} [TopologicalSpace α] [m : MetricSpace β]
    (f : α → β) (h : IsEmbedding f) : MetricSpace α :=
  .replaceTopology (.induced f h.injective m) h.eq_induced

-- INSTANCE (free from Core): Subtype.metricSpace
