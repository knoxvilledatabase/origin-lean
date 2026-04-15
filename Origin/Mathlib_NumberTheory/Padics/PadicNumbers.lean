/-
Extracted from NumberTheory/Padics/PadicNumbers.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# p-adic numbers

This file defines the `p`-adic numbers (rationals) `ℚ_[p]` as
the completion of `ℚ` with respect to the `p`-adic norm.
We show that the `p`-adic norm on `ℚ` extends to `ℚ_[p]`, that `ℚ` is embedded in `ℚ_[p]`,
and that `ℚ_[p]` is Cauchy complete.

## Important definitions

* `Padic` : the type of `p`-adic numbers
* `padicNormE` : the rational-valued `p`-adic norm on `ℚ_[p]`
* `Padic.addValuation` : the additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`

## Notation

We introduce the notation `ℚ_[p]` for the `p`-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct `ℝ`.
`ℚ_[p]` inherits a field structure from this construction.
The extension of the norm on `ℚ` to `ℚ_[p]` is *not* analogous to extending the absolute value to
`ℝ` and hence the proof that `ℚ_[p]` is complete is different from the proof that ℝ is complete.

`padicNormE` is the rational-valued `p`-adic norm on `ℚ_[p]`.
To instantiate `ℚ_[p]` as a normed field, we must cast this into an `ℝ`-valued norm.
The `ℝ`-valued norm, using notation `‖ ‖` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padicNorm` to `padicNormE` when possible.
Since `padicNormE` and `‖ ‖` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

open WithZero

set_option linter.flexible false in

def Rat.padicValuation (p : ℕ) [Fact p.Prime] : Valuation ℚ ℤᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-padicValRat p x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intros
    split_ifs <;>
    simp_all [padicValRat.mul, exp_add, mul_comm]
  map_add_le_max' := by
    intros
    split_ifs
    any_goals simp_all [-exp_neg]
    rw [← min_le_iff]
    exact padicValRat.min_le_padicValRat_add ‹_›

def Int.padicValuation (p : ℕ) [Fact p.Prime] : Valuation ℤ ℤᵐ⁰ :=
  (Rat.padicValuation p).comap (Int.castRingHom ℚ)
