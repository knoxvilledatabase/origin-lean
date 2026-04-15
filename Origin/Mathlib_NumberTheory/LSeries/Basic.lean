/-
Extracted from NumberTheory/LSeries/Basic.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# L-series

Given a sequence `f: ℕ → ℂ`, we define the corresponding L-series.

## Main Definitions

* `LSeries.term f s n` is the `n`th term of the L-series of the sequence `f` at `s : ℂ`.
  We define it to be zero when `n = 0`.

* `LSeries f` is the L-series with a given sequence `f` as its coefficients. This is not the
  analytic continuation (which does not necessarily exist), just the sum of the infinite series if
  it exists and zero otherwise.

* `LSeriesSummable f s` indicates that the L-series of `f` converges at `s : ℂ`.

* `LSeriesHasSum f s a` expresses that the L-series of `f` converges (absolutely) at `s : ℂ` to
  `a : ℂ`.

## Main Results

* `LSeriesSummable_of_isBigO_rpow`: the `LSeries` of a sequence `f` such that `f = O(n^(x-1))`
  converges at `s` when `x < s.re`.

* `LSeriesSummable.isBigO_rpow`: if the `LSeries` of `f` is summable at `s`, then `f = O(n^(re s))`.

## Notation

We introduce `L` as notation for `LSeries` and `↗f` as notation for `fun n : ℕ ↦ (f n : ℂ)`,
both scoped to `LSeries.notation`. The latter makes it convenient to use arithmetic functions
or Dirichlet characters (or anything that coerces to a function `N → R`, where `ℕ` coerces
to `N` and `R` coerces to `ℂ`) as arguments to `LSeries` etc.

## Reference

For some background on the design decisions made when implementing L-series in Mathlib
(and applications motivating the development), see the paper
[Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
by David Loeffler and Michael Stoll.

## Tags

L-series
-/

open Complex

/-!
### The terms of an L-series

We define the `n`th term evaluated at a complex number `s` of the L-series associated
to a sequence `f : ℕ → ℂ`, `LSeries.term f s n`, and provide some basic API.

We set `LSeries.term f s 0 = 0`, and for positive `n`, `LSeries.term f s n = f n / n ^ s`.
-/

namespace LSeries

noncomputable

def term (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else f n / n ^ s

lemma term_def₀ {f : ℕ → ℂ} (hf : f 0 = 0) (s : ℂ) (n : ℕ) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term]
  split_ifs with h <;> simp [h, hf, cpow_neg, div_eq_inv_mul, mul_comm]
