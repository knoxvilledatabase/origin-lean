/-
Extracted from RingTheory/PowerSeries/Catalan.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Catalan Power Series

We introduce the Catalan generating function as a formal power series over `ℕ`:
  `catalanSeries = ∑_{n ≥ 0} catalan n * X^n`

## Main Definitions
* `PowerSeries.catalanSeries`: The Catalan generating function as a power series.

## Main Results
* `PowerSeries.catalanSeries_one_add_X_mul_self_sq`: The Catalan generating function satisfies the
  equation `catalanSeries = 1 + X * catalanSeries ^ 2`.

## TODO
* Find and prove the closed formula for the Catalan generating function:
  `C(X) = (1 - √(1 - 4X)) / (2X)`
-/

open Finset

namespace PowerSeries

def catalanSeries : PowerSeries ℕ := PowerSeries.mk catalan
