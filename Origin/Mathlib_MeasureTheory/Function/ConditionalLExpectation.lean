/-
Extracted from MeasureTheory/Function/ConditionalLExpectation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Conditional Lebesgue expectation

We define the conditional expectation of a `ℝ≥0∞`-valued function using the Lebesgue integral.
Given a measure `P : Measure[mΩ₀] Ω` and a sub-σ-algebra `mΩ` of `mΩ₀` (meaning `hm : mΩ ≤ mΩ₀`)
and a function `X : Ω → ℝ≥0∞`, if `P.trim hm` is σ-finite, then the conditional (Lebesgue)
expectation `P⁻[X|mΩ]` of `X` is the `mΩ`-measurable function such that for all
`mΩ`-measurable sets `s`, `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`
(see `setLIntegral_condLExp`). This is unique up to `P`-ae equality (see `ae_eq_condLExp`).

## Main definitions

* `condLExp` : conditional (Lebesgue) expectation of `X` with respect to `mΩ`.
* `setLIntegral_condLExp`: For any `mΩ`-measurable set `s`,
  `∫⁻ ω in s, P⁻[X|mΩ] ω ∂P = ∫⁻ ω in s, X ω ∂P`.
* `ae_eq_condLExp` : the conditional (Lebesgue) expectation is characterized by its (Lebesgue)
  integral on `mΩ`-measurable sets up to `P`-ae equality.

## Notation

For a measure `P : Measure[mΩ₀] Ω`, and another `mΩ : MeasurableSpace Ω`, we define the notation
* `P⁻[X|mΩ] = condLExp mΩ P X`

## Design decisions

`P⁻[X|mΩ]` is assigned the junk value `0` when either `¬ mΩ ≤ mΩ₀` (`mΩ` is not a sub-σ-algebra)
or `h : mΩ ≤ mΩ₀` but `¬ SigmaFinite (P.trim hm)` (the latter always holds when `P` is a
probability measure). When both these hold, in some sense the "user definition" of `P⁻[X|mΩ]`
should be considered "the" measurable function which satisfies `setLIntegral_condLExp`
(which is proven unique up to `P`-ae measurable equality in `ae_eq_condLExp`). The actual definition
is just used to show existence. However for (potential) convenience the actual definition assigns
`P⁻[X|mΩ] := X` in the case when `X` is `mΩ`-measurable (which can be invoked using
`condLExp_eq_self`).

## To do

* Prove the pullout property
* Prove a dominated convergence theorem.

-/

open MeasureTheory ProbabilityTheory Measure

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ₀ mΩ : MeasurableSpace Ω} {P : Measure[mΩ₀] Ω} {X Y : Ω → ℝ≥0∞}

open Classical in

noncomputable irreducible_def condLExp (mΩ : MeasurableSpace Ω) (P : Measure[mΩ₀] Ω)
    (X : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  if hm : mΩ ≤ mΩ₀ then
    if SigmaFinite (P.trim hm) then
      if Measurable[mΩ] X then X else
      ∂((P.withDensity X).trim hm)/∂(P.trim hm)
    else 0
  else 0
