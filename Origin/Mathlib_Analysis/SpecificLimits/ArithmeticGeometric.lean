/-
Extracted from Analysis/SpecificLimits/ArithmeticGeometric.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Arithmetic-geometric sequences

An arithmetic-geometric sequence is a sequence defined by the recurrence relation
`u (n + 1) = a * u n + b`.

## Main definitions

* `arithGeom a b u₀`: arithmetic-geometric sequence with starting value `u₀` and recurrence relation
  `u (n + 1) = a * u n + b`.

## Main statements

* `arithGeom_eq`: for `a ≠ 1`, `arithGeom a b u₀ n = a ^ n * (u₀ - (b / (1 - a))) + b / (1 - a)`
* `tendsto_arithGeom_atTop_of_one_lt`: if `1 < a` and `b / (1 - a) < u₀`, then `arithGeom a b u₀ n`
  tends to `+∞` as `n` tends to `+∞`.
  `tendsto_arithGeom_nhds_of_lt_one`: if `0 ≤ a < 1`, then `arithGeom a b u₀ n` tends to
  `b / (1 - a)` as `n` tends to `+∞`.
* `arithGeom_strictMono`: if `1 < a` and `b / (1 - a) < u₀`, then `arithGeom a b u₀` is strictly
  monotone.

-/

open Filter Topology

variable {R : Type*} {a b u₀ : R}

def arithGeom [Mul R] [Add R] (a b u₀ : R) : ℕ → R
| 0 => u₀
| n + 1 => a * arithGeom a b u₀ n + b
