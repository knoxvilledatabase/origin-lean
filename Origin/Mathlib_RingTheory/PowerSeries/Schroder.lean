/-
Extracted from RingTheory/PowerSeries/Schroder.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Schröder Numbers Power Series

This file defines lemmas and theorems about the power series for large and small Schröder numbers.

## Main Definitions
* `PowerSeries.largeSchroderSeries`: The power series for large Schröder numbers.
* `PowerSeries.smallSchroderSeries`: The power series for small Schröder numbers.

## Main Results
* `largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq`:
  The functional equation for the large Schröder numbers power series.

## TODO

* Prove the small Schröder numbers power series.

-/

open Finset Nat

namespace PowerSeries

def largeSchroderSeries : PowerSeries ℕ :=
  PowerSeries.mk largeSchroder
