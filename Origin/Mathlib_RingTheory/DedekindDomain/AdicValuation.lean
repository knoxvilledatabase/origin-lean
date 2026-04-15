/-
Extracted from RingTheory/DedekindDomain/AdicValuation.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adic valuations on Dedekind domains
Given a Dedekind domain `R` of Krull dimension 1 and a maximal ideal `v` of `R`, we define the
`v`-adic valuation on `R` and its extension to the field of fractions `K` of `R`.
We prove several properties of this valuation, including the existence of uniformizers.

We define the completion of `K` with respect to the `v`-adic valuation, denoted
`v.adicCompletion`, and its ring of integers, denoted `v.adicCompletionIntegers`.

## Main definitions
- `IsDedekindDomain.HeightOneSpectrum.intValuation v` is the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation v` is the `v`-adic valuation on `K`.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion v` is the completion of `K` with respect
  to its `v`-adic valuation.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers v` is the ring of integers of
  `v.adicCompletion`.
- `IsDedekindDomain.HeightOneSpectrum.adicAbv v` is the `v`-adic absolute value on `K` defined as
  `b` raised to negative `v`-adic valuation, for some `b` in `ℝ≥0`.

## Main results
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_one` : The `v`-adic valuation on `R` is
  bounded above by 1.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than 1 if and only if `v` divides the ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd` : The `v`-adic valuation of
  `r ∈ R` is less than or equal to `WithZero.exp (-n)` if and only if `vⁿ` divides the
  ideal `(r)`.
- `IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer` : There exists `π ∈ R`
  with `v`-adic valuation `WithZero.exp (-1)`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_mk'` : The `v`-adic valuation of `r/s ∈ K`
  is the valuation of `r` divided by the valuation of `s`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap` : The `v`-adic valuation on `K`
  extends the `v`-adic valuation on `R`.
- `IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer` : There exists `π ∈ K` with
  `v`-adic valuation `WithZero.exp (-1)`.

## Implementation notes
We are only interested in Dedekind domains with Krull dimension 1.

## References
* [G. J. Janusz, *Algebraic Number Fields*][janusz1996]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags
dedekind domain, dedekind ring, adic valuation
-/

noncomputable section

open WithZero Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-! ### Adic valuations on the Dedekind domain R -/

open scoped Classical in

def intValuationDef (r : R) : ℤᵐ⁰ :=
  if r = 0 then 0
  else
    exp (-(Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)

theorem intValuationDef_if_pos {r : R} (hr : r = 0) : v.intValuationDef r = 0 :=
  if_pos hr
