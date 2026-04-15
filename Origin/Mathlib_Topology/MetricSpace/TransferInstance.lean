/-
Extracted from Topology/MetricSpace/TransferInstance.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Transfer metric space structures across `Equiv`s

In this file, we transfer a distance and (pseudo-)metric space structure across an equivalence.

-/

variable {α β : Type*}

namespace Equiv

variable (e : α ≃ β)

protected abbrev dist (e : α ≃ β) [Dist β] : Dist α := ⟨fun x y ↦ dist (e x) (e y)⟩

protected abbrev pseudometricSpace [PseudoMetricSpace β] (e : α ≃ β) : PseudoMetricSpace α :=
  .induced e ‹_›

protected abbrev metricSpace [MetricSpace β] (e : α ≃ β) : MetricSpace α :=
  .induced e e.injective ‹_›

end Equiv
