/-
Extracted from MeasureTheory/Group/Pointwise.lean
Genuine: 1 of 3 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `MeasurableSet`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `MeasurableSet.mul` etc.
-/

open Pointwise

open Set

@[to_additive]
theorem MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace G]
    [MeasurableSpace α] [MeasurableSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

-- DISSOLVED: MeasurableSet.const_smul_of_ne_zero

-- DISSOLVED: MeasurableSet.const_smul₀
