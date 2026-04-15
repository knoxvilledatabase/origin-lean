/-
Extracted from MeasureTheory/Measure/CharacteristicFunction/Basic.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space `V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

The integral is expressed as `∫ v, char he hL w v ∂P`, where `char he hL w` is the
bounded continuous function `fun v ↦ e (L v w)` and `he`, `hL` are continuity hypotheses on `e`
and `L`.

## Main definitions

* `innerProbChar`: the bounded continuous map `x ↦ exp(⟪x, t⟫ * I)` in an inner product space.
  This is `char` for the inner product bilinear map and the additive character `e = probChar`.
* `charFun μ t`: the characteristic function of a measure `μ` at `t` in an inner product space `E`.
  This is defined as `∫ x, exp (⟪x, t⟫ * I) ∂μ`, where `⟪x, t⟫` is the inner product on `E`.
  It is equal to `∫ v, innerProbChar w v ∂P` (see `charFun_eq_integral_innerProbChar`).
* `probCharDual`: the bounded continuous map `x ↦ exp (L x * I)`, for a continuous linear form `L`.
* `charFunDual μ L`: the characteristic function of a measure `μ` at `L : Dual ℝ E` in
  a normed space `E`. This is the integral `∫ v, exp (L v * I) ∂μ`.

## Main statements

* `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
* `Measure.ext_of_charFun`: If the characteristic functions `charFun` of two finite measures
  `μ` and `ν` on a complete second-countable inner product space coincide, then `μ = ν`.
* `Measure.ext_of_charFunDual`: If the characteristic functions `charFunDual` of two finite measures
  `μ` and `ν` on a Banach space coincide, then `μ = ν`.

-/

open BoundedContinuousFunction RealInnerProductSpace Real Complex ComplexConjugate WithLp

open scoped ENNReal

namespace BoundedContinuousFunction

variable {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable

def innerProbChar (t : E) : E →ᵇ ℂ :=
  char continuous_probChar (L := innerₗ E) continuous_inner t
