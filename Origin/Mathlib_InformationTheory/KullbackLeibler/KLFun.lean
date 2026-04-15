/-
Extracted from InformationTheory/KullbackLeibler/KLFun.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The real function `fun x ↦ x * log x + 1 - x`

We define `klFun x = x * log x + 1 - x`. That function is notable because the Kullback-Leibler
divergence is an f-divergence for `klFun`. That is, the Kullback-Leibler divergence is an integral
of `klFun` composed with a Radon-Nikodym derivative.

For probability measures, any function `f` that differs from `klFun` by an affine function of the
form `x ↦ a * (x - 1)` would give the same value for the integral
`∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.
However, `klFun` is the particular choice among those that satisfies `klFun 1 = 0` and
`deriv klFun 1 = 0`, which ensures that desirable properties of the Kullback-Leibler divergence
extend to other finite measures: it is nonnegative and zero iff the two measures are equal.

## Main definitions

* `klFun`: the function `fun x : ℝ ↦ x * log x + 1 - x`.

This is a continuous nonnegative, strictly convex function on $[0,∞)$, with minimum value 0 at 1.

## Main statements

* `integrable_klFun_rnDeriv_iff`: For two finite measures `μ ≪ ν`, the function
  `x ↦ klFun (μ.rnDeriv ν x).toReal` is integrable with respect to `ν` iff the log-likelihood ratio
  `llr μ ν` is integrable with respect to `μ`.
* `integral_klFun_rnDeriv`: For two finite measures `μ ≪ ν` such that `llr μ ν` is integrable with
  respect to `μ`,
  `∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`.

-/

open Real MeasureTheory Filter Set

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x

lemma klFun_zero : klFun 0 = 1 := by simp [klFun]

lemma klFun_one : klFun 1 = 0 := by simp [klFun]

lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun :=
  (strictConvexOn_mul_log.add_convexOn (convexOn_const _ (convex_Ici _))).sub_concaveOn
    (concaveOn_id (convex_Ici _))

lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

lemma convexOn_Ioi_klFun : ConvexOn ℝ (Ioi 0) klFun :=
  convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)
