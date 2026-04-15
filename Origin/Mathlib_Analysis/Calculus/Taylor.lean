/-
Extracted from Analysis/Calculus/Taylor.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylorCoeffWithin`: the Taylor coefficient using `iteratedDerivWithin`
* `taylorWithin`: the Taylor polynomial using `iteratedDerivWithin`

## Main statements

* `taylor_tendsto`: Taylor's theorem as a limit
* `taylor_isLittleO`: Taylor's theorem using little-o notation
* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector-valued functions with a
  polynomial bound on the remainder
* `taylor_integral_remainder_of_absolutelyContinuous`,
  `taylor_integral_remainder`: Taylor's theorem with the integral form of the
  remainder

## TODO

* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/

open scoped Interval Topology Nat

open Set

variable {𝕜 E F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀

noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))

noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)

theorem taylorWithin_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]
