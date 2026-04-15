/-
Extracted from RingTheory/PowerSeries/Basic.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Formal power series (in one variable)

This file defines (univariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

Formal power series in one variable are defined from multivariate
power series as `PowerSeries R := MvPowerSeries Unit R`.

The file sets up the (semi)ring structure on univariate power series.

We provide the natural inclusion from polynomials to formal power series.

Additional results can be found in:
* `Mathlib/RingTheory/PowerSeries/Trunc.lean`, truncation of power series;
* `Mathlib/RingTheory/PowerSeries/Inverse.lean`, about inverses of power series,
  and the fact that power series over a local ring form a local ring;
* `Mathlib/RingTheory/PowerSeries/Order.lean`, the order of a power series at 0,
  and application to the fact that power series over an integral domain form an integral domain.

## Implementation notes

Because of its definition,
  `PowerSeries R := MvPowerSeries Unit R`.
a lot of proofs and properties from the multivariate case
can be ported to the single variable case.
However, it means that formal power series are indexed by `Unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they were indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

abbrev PowerSeries (R : Type*) :=
  MvPowerSeries Unit R

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

scoped notation:9000 R "⟦X⟧" => PowerSeries R

section Semiring

variable [Semiring R]

def coeff (n : ℕ) : R⟦X⟧ →ₗ[R] R :=
  MvPowerSeries.coeff (single () n)

def monomial (n : ℕ) : R →ₗ[R] R⟦X⟧ :=
  MvPowerSeries.monomial (single () n)

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) :
    coeff (R := R) n = MvPowerSeries.coeff s := by
  rw [coeff, ← h, ← Finsupp.unique_single s]
