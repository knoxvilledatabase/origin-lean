/-
Extracted from MeasureTheory/Function/EssSup.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see `Mathlib/MeasureTheory/Function/AEEqFun.lean`).

## Main definitions

* `essSup f μ := (ae μ).limsup f`
* `essInf f μ := (ae μ).liminf f`
-/

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace

open scoped ENNReal NNReal

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {f : α → β}

def essSup {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).limsup f

def essInf {_ : MeasurableSpace α} (f : α → β) (μ : Measure α) :=
  (ae μ).liminf f

theorem essSup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg

theorem essInf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @essSup_congr_ae α βᵒᵈ _ _ _ _ _ hfg
