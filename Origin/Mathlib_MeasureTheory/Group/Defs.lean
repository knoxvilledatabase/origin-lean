/-
Extracted from MeasureTheory/Group/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Definitions about invariant measures

In this file we define typeclasses for measures invariant under (scalar) multiplication.

- `MeasureTheory.SMulInvariantMeasure M α μ`
  says that the measure `μ` is invariant under scalar multiplication by `c : M`;
- `MeasureTheory.VAddInvariantMeasure M α μ` is the additive version of this typeclass;
- `MeasureTheory.Measure.IsMulLeftInvariant μ`, `MeasureTheory.Measure.IsMulRightInvariant μ`
  say that the measure `μ` is invariant under multiplication on the left and on the right,
  respectively.
- `MeasureTheory.Measure.IsAddLeftInvariant μ`, `MeasureTheory.Measure.IsAddRightInvariant μ`
  are the additive versions of these typeclasses.

For basic facts about the first two typeclasses, see `Mathlib/MeasureTheory/Group/Action`.
For facts about left/right-invariant measures, see `Mathlib/MeasureTheory/Group/Measure`.

## Implementation Notes

The `smul`/`vadd` typeclasses and the left/right multiplication typeclasses
were defined by different people with different tastes,
so the former explicitly use measures of the preimages,
while the latter use `MeasureTheory.Measure.map`.

If the left/right multiplication is measurable
(which is the case in most if not all interesting examples),
these definitions are equivalent.

The definitions that use `MeasureTheory.Measure.map`
imply that the left (resp., right) multiplication is `AEMeasurable`.
-/

assert_not_exists Module.Basis

namespace MeasureTheory

class VAddInvariantMeasure (M α : Type*) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_vadd : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s
