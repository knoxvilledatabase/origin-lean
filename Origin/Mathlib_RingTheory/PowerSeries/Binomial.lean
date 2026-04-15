/-
Extracted from RingTheory/PowerSeries/Binomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binomial Power Series
We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

## Main Definitions
* `PowerSeries.binomialSeries`: A power series expansion of `(1 + X) ^ r`, where `r` is an element
  of a commutative binomial ring `R`.

## Main Results
* `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.
* `PowerSeries.binomialSeries_nat`: when `r` is a natural number, we get `(1 + X) ^ r`.
* `PowerSeries.rescale_neg_one_invOneSubPow`: The image of `(1 - X) ^ (-d)` under the map
  `X ↦ (-X)` is `(1 + X) ^ (-d)`

## TODO
* When `A` is a commutative `R`-algebra, the exponentiation action makes the multiplicative group
  `1 + XA[[X]]` into an `R`-module.

-/

open Finset

suppress_compilation

variable {R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1
