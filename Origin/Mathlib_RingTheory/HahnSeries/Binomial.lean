/-
Extracted from RingTheory/HahnSeries/Binomial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Binomial expansions of powers of Hahn Series
We introduce binomial expansions using `embDomain`.

## Main Definitions
  * `HahnSeries.binomialFamily`

## Main results
  * coefficients of powers of binomials

-/

noncomputable section

namespace HahnSeries

variable {Γ R A : Type*}

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]
  [BinomialRing R]

namespace SummableFamily

variable [CommRing A] [Algebra R A]

def binomialFamily (x : A⟦Γ⟧) (r : R) :
    SummableFamily Γ A ℕ :=
  powerSeriesFamily (x - 1) (PowerSeries.binomialSeries A r)
