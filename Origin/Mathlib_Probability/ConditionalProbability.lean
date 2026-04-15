/-
Extracted from Probability/ConditionalProbability.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Conditional Probability

This file defines conditional probability and includes basic results relating to it.

Given some measure `μ` defined on a measure space on some type `Ω` and some `s : Set Ω`,
we define the measure of `μ` conditioned on `s` as the restricted measure scaled by
the inverse of the measure of `s`: `cond μ s = (μ s)⁻¹ • μ.restrict s`. The scaling
ensures that this is a probability measure (when `μ` is a finite measure).

From this definition, we derive the "axiomatic" definition of conditional probability
based on application: for any `s t : Set Ω`, we have `μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`.

## Main Statements

* `cond_cond_eq_cond_inter`: conditioning on one set and then another is equivalent
  to conditioning on their intersection.
* `cond_eq_inv_mul_cond_mul`: Bayes' Theorem, `μ[t | s] = (μ s)⁻¹ * μ[s | t] * (μ t)`.

## Notation

This file uses the notation `μ[|s]` the measure of `μ` conditioned on `s`,
and `μ[t | s]` for the probability of `t` given `s` under `μ` (equivalent to the
application `μ[|s] t`).

These notations are contained in the scope `ProbabilityTheory`.

## Implementation notes

Because we have the alternative measure restriction application principles
`Measure.restrict_apply` and `Measure.restrict_apply'`, which require
measurability of the restricted and restricting sets, respectively,
many of the theorems here will have corresponding alternatives as well.
For the sake of brevity, we've chosen to only go with `Measure.restrict_apply'`
for now, but the alternative theorems can be added if needed.

Use of `@[simp]` generally follows the rule of removing conditions on a measure
when possible.

Hypotheses that are used to "define" a conditional distribution by requiring that
the conditioning set has non-zero measure should be named using the abbreviation
"c" (which stands for "conditionable") rather than "nz". For example `(hci : μ (s ∩ t) ≠ 0)`
(rather than `hnzi`) should be used for a hypothesis ensuring that `μ[|s ∩ t]` is defined.

## Tags

conditional, conditioned, bayes
-/

noncomputable section

open ENNReal MeasureTheory MeasureTheory.Measure MeasurableSpace Set

variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}

namespace ProbabilityTheory

variable (μ) in

def cond (s : Set Ω) : Measure Ω :=
  (μ s)⁻¹ • μ.restrict s
