/-
Extracted from RingTheory/Nullstellensatz.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `MvPolynomial`s.
The main statement of the theorem is `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`.

The statement is in terms of new definitions `vanishingIdeal` and `zeroLocus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishingIdeal` and `zeroLocus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/

open Ideal

noncomputable section

namespace MvPolynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

variable (K) in

def zeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → K) :=
  {x : σ → K | ∀ p ∈ I, aeval x p = 0}
