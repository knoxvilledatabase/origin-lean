/-
Extracted from Topology/MetricSpace/Defs.lean
Genuine: 23 | Conflates: 0 | Dissolved: 0 | Infrastructure: 21
-/
import Origin.Core
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section

/-!
# Metric spaces

This file defines metric spaces and shows some of their basic properties.

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. This includes open and closed sets, compactness, completeness, continuity
and uniform continuity.

TODO (anyone): Add "Main results" section.

## Implementation notes
A lot of elementary properties don't require `eq_of_dist_eq_zero`, hence are stated and proven
for `PseudoMetricSpace`s in `PseudoMetric.lean`.

## Tags

metric, pseudo_metric, dist
-/

open Set Filter Bornology

open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

variable [PseudoMetricSpace α]

class MetricSpace (α : Type u) extends PseudoMetricSpace α : Type u where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y

@[ext]
theorem MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption

def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }

variable {γ : Type w} [MetricSpace γ]

theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y :=
  MetricSpace.eq_of_dist_eq_zero

@[simp]
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y :=
  Iff.intro eq_of_dist_eq_zero fun this => this ▸ dist_self _

@[simp]
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by rw [eq_comm, dist_eq_zero]

theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y := by
  simpa only [not_iff_not] using dist_eq_zero

@[simp]
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y := by
  simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp]
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y := by
  simpa only [not_le] using not_congr dist_le_zero

theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y :=
  eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

theorem eq_of_nndist_eq_zero {x y : γ} : nndist x y = 0 → x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

@[simp]
theorem nndist_eq_zero {x y : γ} : nndist x y = 0 ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, dist_eq_zero]

@[simp]
theorem zero_eq_nndist {x y : γ} : 0 = nndist x y ↔ x = y := by
  simp only [NNReal.eq_iff, ← dist_nndist, imp_self, NNReal.coe_zero, zero_eq_dist]

namespace Metric

variable {x : γ} {s : Set γ}

@[simp] theorem closedBall_zero : closedBall x 0 = {x} := Set.ext fun _ => dist_le_zero

@[simp] theorem sphere_zero : sphere x 0 = {x} := Set.ext fun _ => dist_eq_zero

theorem subsingleton_closedBall (x : γ) {r : ℝ} (hr : r ≤ 0) : (closedBall x r).Subsingleton := by
  rcases hr.lt_or_eq with (hr | rfl)
  · rw [closedBall_eq_empty.2 hr]
    exact subsingleton_empty
  · rw [closedBall_zero]
    exact subsingleton_singleton

theorem subsingleton_sphere (x : γ) {r : ℝ} (hr : r ≤ 0) : (sphere x r).Subsingleton :=
  (subsingleton_closedBall x hr).anti sphere_subset_closedBall

end Metric

abbrev MetricSpace.replaceUniformity {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : MetricSpace γ where
  toPseudoMetricSpace := PseudoMetricSpace.replaceUniformity m.toPseudoMetricSpace H
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _

theorem MetricSpace.replaceUniformity_eq {γ} [U : UniformSpace γ] (m : MetricSpace γ)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace]) : m.replaceUniformity H = m := by
  ext; rfl

abbrev MetricSpace.replaceTopology {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) : MetricSpace γ :=
  @MetricSpace.replaceUniformity γ (m.toUniformSpace.replaceTopology H) m rfl

theorem MetricSpace.replaceTopology_eq {γ} [U : TopologicalSpace γ] (m : MetricSpace γ)
    (H : U = m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) :
    m.replaceTopology H = m := by
  ext; rfl

abbrev MetricSpace.replaceBornology {α} [B : Bornology α] (m : MetricSpace α)
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) : MetricSpace α :=
  { PseudoMetricSpace.replaceBornology _ H, m with toBornology := B }

theorem MetricSpace.replaceBornology_eq {α} [m : MetricSpace α] [B : Bornology α]
    (H : ∀ s, @IsBounded _ B s ↔ @IsBounded _ PseudoMetricSpace.toBornology s) :
    MetricSpace.replaceBornology _ H = m := by
  ext
  rfl

instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _

instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp +contextual [principal_univ, eq_top_of_neBot (𝓤 PUnit)]

/-!
### `Additive`, `Multiplicative`

The distance on those type synonyms is inherited without change.
-/

open Additive Multiplicative

section

variable [Dist X]

instance : Dist (Additive X) := ‹Dist X›

instance : Dist (Multiplicative X) := ‹Dist X›

@[simp] theorem dist_ofMul (a b : X) : dist (ofMul a) (ofMul b) = dist a b := rfl

@[simp] theorem dist_ofAdd (a b : X) : dist (ofAdd a) (ofAdd b) = dist a b := rfl

@[simp] theorem dist_toMul (a b : Additive X) : dist a.toMul b.toMul = dist a b := rfl

@[simp] theorem dist_toAdd (a b : Multiplicative X) : dist a.toAdd b.toAdd = dist a b := rfl

end

section

variable [PseudoMetricSpace X]

@[simp] theorem nndist_ofMul (a b : X) : nndist (ofMul a) (ofMul b) = nndist a b := rfl

@[simp] theorem nndist_ofAdd (a b : X) : nndist (ofAdd a) (ofAdd b) = nndist a b := rfl

@[simp] theorem nndist_toMul (a b : Additive X) : nndist a.toMul b.toMul = nndist a b := rfl

@[simp]
theorem nndist_toAdd (a b : Multiplicative X) : nndist a.toAdd b.toAdd = nndist a b := rfl

end

instance [MetricSpace X] : MetricSpace (Additive X) := ‹MetricSpace X›

instance [MetricSpace X] : MetricSpace (Multiplicative X) := ‹MetricSpace X›

/-!
### Order dual

The distance on this type synonym is inherited without change.
-/

open OrderDual

section

variable [Dist X]

instance : Dist Xᵒᵈ := ‹Dist X›

@[simp] theorem dist_toDual (a b : X) : dist (toDual a) (toDual b) = dist a b := rfl

@[simp] theorem dist_ofDual (a b : Xᵒᵈ) : dist (ofDual a) (ofDual b) = dist a b := rfl

end

section

variable [PseudoMetricSpace X]

instance : PseudoMetricSpace Xᵒᵈ := ‹PseudoMetricSpace X›

@[simp] theorem nndist_toDual (a b : X) : nndist (toDual a) (toDual b) = nndist a b := rfl

@[simp] theorem nndist_ofDual (a b : Xᵒᵈ) : nndist (ofDual a) (ofDual b) = nndist a b := rfl

end

instance [MetricSpace X] : MetricSpace Xᵒᵈ := ‹MetricSpace X›
