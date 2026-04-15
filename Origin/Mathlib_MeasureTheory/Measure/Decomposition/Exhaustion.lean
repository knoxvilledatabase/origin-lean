/-
Extracted from MeasureTheory/Measure/Decomposition/Exhaustion.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Method of exhaustion

If `μ, ν` are two measures with `ν` s-finite, then there exists a set `s` such that
`μ` is sigma-finite on `s`, and for all sets `t ⊆ sᶜ`, either `ν t = 0` or `μ t = ∞`.

## Main definitions

* `MeasureTheory.Measure.sigmaFiniteSetWRT`: if such a set exists, `μ.sigmaFiniteSetWRT ν` is
  a measurable set such that `μ.restrict (μ.sigmaFiniteSetWRT ν)` is sigma-finite and
  for all sets `t ⊆ (μ.sigmaFiniteSetWRT ν)ᶜ`, either `ν t = 0` or `μ t = ∞`.
  If no such set exists (which is only possible if `ν` is not s-finite), we define
  `μ.sigmaFiniteSetWRT ν = ∅`.
* `MeasureTheory.Measure.sigmaFiniteSet`: for an s-finite measure `μ`, a measurable set such that
  `μ.restrict μ.sigmaFiniteSet` is sigma-finite, and for all sets `s ⊆ μ.sigmaFiniteSetᶜ`,
  either `μ s = 0` or `μ s = ∞`.
  Defined as `μ.sigmaFiniteSetWRT μ`.

## Main statements

* `measure_eq_top_of_subset_compl_sigmaFiniteSetWRT`: for s-finite `ν`, for all sets `s`
  in `(sigmaFiniteSetWRT μ ν)ᶜ`, if `ν s ≠ 0` then `μ s = ∞`.
* An instance showing that `μ.restrict (sigmaFiniteSetWRT μ ν)` is sigma-finite.
* `restrict_compl_sigmaFiniteSetWRT`: if `μ ≪ ν` and `ν` is s-finite, then
  `μ.restrict (μ.sigmaFiniteSetWRT ν)ᶜ = ∞ • ν.restrict (μ.sigmaFiniteSetWRT ν)ᶜ`. As a consequence,
  that restriction is s-finite.

* An instance showing that `μ.restrict μ.sigmaFiniteSet` is sigma-finite.
* `restrict_compl_sigmaFiniteSet_eq_zero_or_top`: the measure `μ.restrict μ.sigmaFiniteSetᶜ` takes
  only two values: 0 and ∞ .
* `measure_compl_sigmaFiniteSet_eq_zero_iff_sigmaFinite`: a measure `μ` is sigma-finite
  iff `μ μ.sigmaFiniteSetᶜ = 0`.

## References

* [P. R. Halmos, *Measure theory*, 17.3 and 30.11][halmos1950measure]

-/

assert_not_exists MeasureTheory.Measure.rnDeriv

assert_not_exists MeasureTheory.VectorMeasure

open scoped ENNReal Topology

open Filter

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {s t : Set α}

open Classical in

def Measure.sigmaFiniteSetWRT (μ ν : Measure α) : Set α :=
  if h : ∃ s : Set α, MeasurableSet s ∧ SigmaFinite (μ.restrict s)
    ∧ (∀ t, t ⊆ sᶜ → ν t ≠ 0 → μ t = ∞)
  then h.choose
  else ∅
