/-
Extracted from MeasureTheory/Function/StronglyMeasurable/Lp.lean
Genuine: 1 | Conflates: 0 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `Memℒp.aefinStronglyMeasurable`: if `Memℒp f p μ` with `0 < p < ∞`, then
  `AEFinStronglyMeasurable f μ`.
* `Lp.finStronglyMeasurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
Springer, 2016.
-/

open MeasureTheory Filter TopologicalSpace Function

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α → G}

-- DISSOLVED: Memℒp.finStronglyMeasurable_of_stronglyMeasurable

-- DISSOLVED: Memℒp.aefinStronglyMeasurable

theorem Integrable.aefinStronglyMeasurable (hf : Integrable f μ) : AEFinStronglyMeasurable f μ :=
  (memℒp_one_iff_integrable.mpr hf).aefinStronglyMeasurable one_ne_zero ENNReal.coe_ne_top

-- DISSOLVED: Lp.finStronglyMeasurable

end MeasureTheory
