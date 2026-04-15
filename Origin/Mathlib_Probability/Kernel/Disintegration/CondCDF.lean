/-
Extracted from Probability/Kernel/Disintegration/CondCDF.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conditional cumulative distribution function

Given `ρ : Measure (α × ℝ)`, we define the conditional cumulative distribution function
(conditional cdf) of `ρ`. It is a function `condCDF ρ : α → ℝ → ℝ` such that if `ρ` is a finite
measure, then for all `a : α` `condCDF ρ a` is monotone and right-continuous with limit 0 at -∞
and limit 1 at +∞, and such that for all `x : ℝ`, `a ↦ condCDF ρ a x` is measurable. For all
`x : ℝ` and measurable set `s`, that function satisfies
`∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

`condCDF` is build from the more general tools about kernel CDFs developed in the file
`Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean`. In that file, we build a function
`α × β → StieltjesFunction ℝ` (which is `α × β → ℝ → ℝ` with additional properties) from a function
`α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some properties like measurability more
easily. Here we apply that construction to the case `β = Unit` and then drop `β` to build
`condCDF : α → StieltjesFunction ℝ`.

## Main definitions

* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction ℝ`: the conditional cdf of
  `ρ : Measure (α × ℝ)`. A `StieltjesFunction ℝ` is a function `ℝ → ℝ` which is monotone and
  right-continuous.

## Main statements

* `ProbabilityTheory.setLIntegral_condCDF`: for all `a : α` and `x : ℝ`, all measurable set `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

-/

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} (ρ : Measure (α × ℝ))

noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst

theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs, restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic),
    univ_prod, Set.prod_eq]

theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ
