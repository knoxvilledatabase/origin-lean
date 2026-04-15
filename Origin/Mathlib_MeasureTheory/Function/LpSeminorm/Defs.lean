/-
Extracted from MeasureTheory/Function/LpSeminorm/Defs.lean
Genuine: 3 of 8 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `eLpNorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `MemLp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `eLpNorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `eLpNormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `essSup ‖f‖ μ`.
* `eLpNorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `eLpNorm' f p μ`
  for `0 < p < ∞` and to `eLpNormEssSup f μ` for `p = ∞`.

* `MemLp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`eLpNorm f p μ < ∞`)

-/

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {f : α → E}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `eLpNorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `eLpNorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `eLpNormEssSup f μ`).

We also define a predicate `MemLp f p μ`, requesting that a function is almost everywhere
measurable and has finite `eLpNorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `eLpNorm'` and `eLpNormEssSup` when it makes sense,
deduce it for `eLpNorm`, and translate it in terms of `MemLp`.
-/

def eLpNorm' {_ : MeasurableSpace α} (f : α → ε) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)

def eLpNormEssSup (f : α → ε) (μ : Measure α) :=
  essSup (fun x => ‖f x‖ₑ) μ

def eLpNorm {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

variable {μ ν : Measure α}

-- DISSOLVED: eLpNorm_eq_eLpNorm'

-- DISSOLVED: eLpNorm_nnreal_eq_eLpNorm'

-- DISSOLVED: eLpNorm_eq_lintegral_rpow_enorm_toReal
