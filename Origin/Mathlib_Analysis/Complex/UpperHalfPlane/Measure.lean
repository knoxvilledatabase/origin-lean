/-
Extracted from Analysis/Complex/UpperHalfPlane/Measure.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Invariant measure on the upper half-plane

We equip the upper half-plane with a measure, defined as the restriction of the usual measure
on `ℂ` weighted by the function `1 / (im z) ^ 2`. We show that this measure is invariant under
the action of `GL(2, ℝ)`.
-/

open MeasureTheory

open scoped NNReal

public noncomputable section

namespace UpperHalfPlane

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding
