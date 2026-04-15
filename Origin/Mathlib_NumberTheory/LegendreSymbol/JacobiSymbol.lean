/-
Extracted from NumberTheory/LegendreSymbol/JacobiSymbol.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobiSym a b`, for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `legendreSym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `Nat.factors`. Since `Nat.factors 0 = []`,
this implies in particular that `jacobiSym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Jacobi symbol, including the following.

* Multiplicativity in both arguments (`jacobiSym.mul_left`, `jacobiSym.mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobiSym.eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobiSym.eq_zero_iff_not_coprime`)

* If the symbol has the value `-1`, then `a : ZMod b` is not a square
  (`ZMod.nonsquare_of_jacobiSym_eq_neg_one`); the converse holds when `b = p` is a prime
  (`ZMod.nonsquare_iff_jacobiSym_eq_neg_one`); in particular, in this case `a` is a
  square mod `p` when the symbol has the value `1` (`ZMod.isSquare_of_jacobiSym_eq_one`).

* Quadratic reciprocity (`jacobiSym.quadratic_reciprocity`,
  `jacobiSym.quadratic_reciprocity_one_mod_four`,
  `jacobiSym.quadratic_reciprocity_three_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobiSym.at_neg_one`,
  `jacobiSym.at_two`, `jacobiSym.at_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobiSym.mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobiSym.mod_right`)

* A `csimp` rule for `jacobiSym` and `legendreSym` that evaluates `J(a | b)` efficiently by
  reducing to the case `0 ≤ a < b` and `a`, `b` odd, and then swaps `a`, `b` and recurses using
  quadratic reciprocity.

## Notation

We define the notation `J(a | b)` for `jacobiSym a b`, localized to `NumberTheorySymbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

section Jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol $\Bigl(\frac{a}{b}\Bigr)$ for integers `a` and natural numbers `b`
as the product of the Legendre symbols $\Bigl(\frac{a}{p}\Bigr)$, where `p` runs through the
prime divisors (with multiplicity) of `b`, as provided by `b.factors`. This agrees with the
Jacobi symbol when `b` is odd and gives less meaningful values when it is not (e.g., the symbol
is `1` when `b = 0`). This is called `jacobiSym a b`.

We define localized notation (scope `NumberTheorySymbols`) `J(a | b)` for the Jacobi
symbol `jacobiSym a b`.
-/

open Nat ZMod

def jacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  (b.primeFactorsList.pmap (fun p pp => @legendreSym p ⟨pp⟩ a) fun _ pf =>
    prime_of_mem_primeFactorsList pf).prod
