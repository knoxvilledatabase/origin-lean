/-
Extracted from Topology/Instances/Discrete.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Instances related to the discrete topology

We prove that the discrete topology is
* first-countable,
* second-countable for an encodable type,
* equal to the order topology in linear orders which are also `PredOrder` and `SuccOrder`,
* metrizable.

When importing this file and `Data.Nat.SuccPred`, the instances `SecondCountableTopology ℕ`
and `OrderTopology ℕ` become available.

-/

open Order Set TopologicalSpace Filter

variable {α : Type*} [TopologicalSpace α]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

theorem LinearOrder.bot_topologicalSpace_eq_generateFrom {α} [LinearOrder α] [PredOrder α]
    [SuccOrder α] : (⊥ : TopologicalSpace α) = generateFrom { s | ∃ a, s = Ioi a ∨ s = Iio a } := by
  let _ := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  exact DiscreteTopology.of_predOrder_succOrder.eq_bot.symm

theorem discreteTopology_iff_orderTopology_of_pred_succ [LinearOrder α] [PredOrder α]
    [SuccOrder α] : DiscreteTopology α ↔ OrderTopology α := by
  refine ⟨fun h ↦ ⟨?_⟩, fun h ↦ .of_predOrder_succOrder⟩
  rw [h.eq_bot, LinearOrder.bot_topologicalSpace_eq_generateFrom]

-- INSTANCE (free from Core): OrderTopology.of_discreteTopology

-- INSTANCE (free from Core): OrderTopology.of_linearLocallyFinite
