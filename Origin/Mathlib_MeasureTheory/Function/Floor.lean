/-
Extracted from MeasureTheory/Function/Floor.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `Int.floor`, `Int.ceil`, `Int.fract`, `Nat.floor`, and `Nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/

open Set

section FloorRing

variable {α R : Type*} [MeasurableSpace α] [Ring R] [LinearOrder R] [FloorRing R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R]

theorem Int.measurable_floor [OpensMeasurableSpace R] : Measurable (Int.floor : R → ℤ) :=
  measurable_to_countable fun x => by
    simpa only [Int.preimage_floor_singleton] using measurableSet_Ico
