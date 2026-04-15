/-
Extracted from Probability/Independence/Integrable.lean
Genuine: 1 | Conflates: 0 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Function.L1Space
import Mathlib.Probability.Independence.Basic

/-!
# Independence of functions implies that the measure is a probability measure

If a nonzero function belongs to `ℒ^p` (in particular if it is integrable) and is independent
of another function, then the space is a probability space.

-/

open Filter ProbabilityTheory

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {Ω E F: Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F]

-- DISSOLVED: Memℒp.isProbabilityMeasure_of_indepFun

lemma Integrable.isProbabilityMeasure_of_indepFun (f : Ω → E) (g : Ω → F)
    (hf : Integrable f μ) (h'f : ¬ (∀ᵐ ω ∂μ, f ω = 0)) (hindep : IndepFun f g μ) :
    IsProbabilityMeasure μ :=
  Memℒp.isProbabilityMeasure_of_indepFun f g one_ne_zero ENNReal.one_ne_top
    (memℒp_one_iff_integrable.mpr hf) h'f hindep

end MeasureTheory
