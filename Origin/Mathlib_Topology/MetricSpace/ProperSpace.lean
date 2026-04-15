/-
Extracted from Topology/MetricSpace/ProperSpace.lean
Genuine: 5 of 18 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-! ## Proper spaces

## Main definitions and results
* `ProperSpace α`: a `PseudoMetricSpace` where all closed balls are compact

* `isCompact_sphere`: any sphere in a proper space is compact.
* `proper_of_compact`: compact spaces are proper.
* `secondCountable_of_proper`: proper spaces are sigma-compact, hence second countable.
* `locallyCompact_of_proper`: proper spaces are locally compact.
* `pi_properSpace`: finite products of proper spaces are proper.

-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section ProperSpace

open Metric

class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)

export ProperSpace (isCompact_closedBall)

theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

-- INSTANCE (free from Core): {α

-- INSTANCE (free from Core): Metric.sphere.compactSpace

variable [PseudoMetricSpace α]

-- INSTANCE (free from Core): (priority

theorem ProperSpace.of_isCompact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

theorem ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β → ℝ}
    (hr : Tendsto r l atTop) (hc : ∀ᶠ i in l, IsCompact (closedBall x (r i))) :
    ProperSpace α where
  isCompact_closedBall a r :=
    let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
    hci.of_isClosed_subset isClosed_closedBall <| closedBall_subset_closedBall' hir

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): prod_properSpace

-- INSTANCE (free from Core): pi_properSpace

lemma ProperSpace.of_isClosed {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} (hs : IsClosed s) :
    ProperSpace s :=
  ⟨fun x r ↦ Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

end ProperSpace

-- INSTANCE (free from Core): [PseudoMetricSpace

-- INSTANCE (free from Core): [PseudoMetricSpace

-- INSTANCE (free from Core): [PseudoMetricSpace
