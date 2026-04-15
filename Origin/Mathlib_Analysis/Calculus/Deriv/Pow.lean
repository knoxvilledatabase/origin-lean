/-
Extracted from Analysis/Calculus/Deriv/Pow.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Derivative of `(f x) ^ n`, `n : ℕ`

In this file we prove that the Fréchet derivative of `fun x => f x ^ n`,
where `n` is a natural number, is `n * f x ^ (n - 1) * f'`.
Additionally, we prove the case for non-commutative rings (with primed names like `deriv_pow'`),
where the result is instead `∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

variable {𝕜 𝔸 : Type*}

section NormedRing

variable [NontriviallyNormedField 𝕜] [NormedRing 𝔸]

variable [NormedAlgebra 𝕜 𝔸] {f : 𝕜 → 𝔸} {f' : 𝔸} {x : 𝕜} {s : Set 𝕜}

theorem HasStrictDerivAt.fun_pow' (h : HasStrictDerivAt f f' x) (n : ℕ) :
    HasStrictDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  simpa using h.hasStrictFDerivAt.pow' n |>.hasStrictDerivAt

theorem HasDerivWithinAt.fun_pow' (h : HasDerivWithinAt f f' s x) (n : ℕ) :
    HasDerivWithinAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) s x := by
  simpa using h.hasFDerivWithinAt.pow' n |>.hasDerivWithinAt

theorem HasDerivAt.fun_pow' (h : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun x ↦ f x ^ n)
      (∑ i ∈ Finset.range n, f x ^ (n.pred - i) * f' * f x ^ i) x := by
  simpa using h.hasFDerivAt.pow' n |>.hasDerivAt
