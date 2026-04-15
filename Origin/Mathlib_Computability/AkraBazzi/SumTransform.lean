/-
Extracted from Computability/AkraBazzi/SumTransform.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Akra-Bazzi theorem: the sum transform

We develop further preliminaries required for the theorem, up to the sum transform.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above, together with basic bounds on `r i n`
  and positivity of `T`.
* `AkraBazziRecurrence.smoothingFn`: the smoothing function $\varepsilon(x) = 1 / \log x$ used in
  the inductive estimates, along with monotonicity, differentiability, and asymptotic properties.
* `AkraBazziRecurrence.p`: the unique Akra–Bazzi exponent characterized by $\sum_i a_i\,(b_i)^p = 1$
  and supporting analytical lemmas such as continuity and injectivity of the defining sum.
* `AkraBazziRecurrence.sumTransform`: the transformation that turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)` and its eventual comparison with multiples of `g n`.
* `AkraBazziRecurrence.asympBound`: the asymptotic bound satisfied by an Akra-Bazzi recurrence,
  namely `n^p (1 + ∑ g(u) / u^(p+1))`, together with positivity statements along the branches
  `r i n`.


## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

open Finset Real Filter Asymptotics

open scoped Topology

/-!
### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence relation
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : ℕ → ℝ) (g : ℝ → ℝ) (a : α → ℝ) (b : α → ℝ) (r : α → ℕ → ℕ) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : ℕ
  /-- `n₀` is always positive -/
  n₀_gt_zero : 0 < n₀
  /-- The coefficients `a i` are positive. -/
  a_pos : ∀ i, 0 < a i
  /-- The coefficients `b i` are positive. -/
  b_pos : ∀ i, 0 < b i
  /-- The coefficients `b i` are less than 1. -/
  b_lt_one : ∀ i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : ∀ x ≥ 0, 0 ≤ g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : ℕ) (hn₀ : n₀ ≤ n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : ℕ) (hn : n < n₀) : 0 < T n
  /-- The functions `r i` always reduce `n`. -/
  r_lt_n : ∀ i n, n₀ ≤ n → r i n < n
  /-- The functions `r i` approximate the values `b i * n`. -/
  dist_r_b : ∀ i, (fun n => (r i n : ℝ) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

noncomputable def min_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_min b

noncomputable def max_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_max b
