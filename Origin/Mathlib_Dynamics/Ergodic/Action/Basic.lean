/-
Extracted from Dynamics/Ergodic/Action/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodic group actions

A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/

open Set Filter MeasureTheory MulAction

open scoped Pointwise

class ErgodicVAdd (G α : Type*) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α)
    extends VAddInvariantMeasure G α μ : Prop where
  aeconst_of_forall_preimage_vadd_ae_eq {s : Set α} : MeasurableSet s →
    (∀ g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) → EventuallyConst s (ae μ)
