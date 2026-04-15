/-
Extracted from RingTheory/MvPowerSeries/Basic.lean
Genuine: 3 of 13 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Formal (multivariate) power series

This file defines multivariate formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from multivariate polynomials to multivariate formal power series.

## Main definitions

- `MvPowerSeries.C`: constant power series

- `MvPowerSeries.X`: the indeterminates

- `MvPowerSeries.coeff`, `MvPowerSeries.constantCoeff`:
  the coefficients of a `MvPowerSeries`, its constant coefficient

- `MvPowerSeries.monomial`: the monomials

- `MvPowerSeries.coeff_mul`: computes the coefficients of the product of two `MvPowerSeries`

- `MvPowerSeries.coeff_prod` : computes the coefficients of products of `MvPowerSeries`

- `MvPowerSeries.coeff_pow` : computes the coefficients of powers of a `MvPowerSeries`

- `MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent`: if the constant coefficient
  of a `MvPowerSeries` is nilpotent, then some coefficients of its powers are automatically zero

- `MvPowerSeries.map`: apply a `RingHom` to the coefficients of a `MvPowerSeries` (as a `RingHom`).

- `MvPowerSeries.X_pow_dvd_iff`, `MvPowerSeries.X_dvd_iff`: equivalent
  conditions for (a power of) an indeterminate to divide a `MvPowerSeries`

- `MvPolynomial.toMvPowerSeries`: the canonical coercion from `MvPolynomial` to `MvPowerSeries`


## Note

This file sets up the (semi)ring structure on multivariate power series:
additional results are in:
* `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` : invertibility,
  formal power series over a local ring form a local ring;
* `Mathlib/RingTheory/MvPowerSeries/Trunc.lean`: truncation of power series.

In `Mathlib/RingTheory/PowerSeries/Basic.lean`, formal power series in one variable
will be obtained as a particular case, defined by
  `PowerSeries R := MvPowerSeries Unit R`.
See that file for a specific description.

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`MvPowerSeries σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

def MvPowerSeries (σ : Type*) (R : Type*) :=
  (σ →₀ ℕ) → R

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

-- INSTANCE (free from Core): [Inhabited

-- INSTANCE (free from Core): [Zero

-- INSTANCE (free from Core): [AddMonoid

-- INSTANCE (free from Core): [AddGroup

-- INSTANCE (free from Core): [AddCommMonoid

-- INSTANCE (free from Core): [AddCommGroup

-- INSTANCE (free from Core): [Nontrivial

-- INSTANCE (free from Core): {A}

-- INSTANCE (free from Core): {A

section Semiring

variable [Semiring R]

def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  letI := Classical.decEq σ
  LinearMap.single R (fun _ ↦ R) n

def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n
