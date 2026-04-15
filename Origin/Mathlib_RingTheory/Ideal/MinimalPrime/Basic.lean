/-
Extracted from RingTheory/Ideal/MinimalPrime/Basic.lean
Genuine: 5 of 7 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal.

## Main results
- `Ideal.minimalPrimes`: `I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
- `minimalPrimes`: `minimalPrimes R` is the set of minimal primes of `R`.
- `Ideal.exists_minimalPrimes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `Ideal.radical_minimalPrimes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `Ideal.sInf_minimalPrimes`: The intersection of minimal primes over `I` is `I.radical`.

Further results that need the theory of localizations can be found in
`Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`.

-/

assert_not_exists Localization -- See `Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (I J : Ideal R)

protected def Ideal.minimalPrimes : Set (Ideal R) :=
  {p | Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) p}

variable (R) in

def minimalPrimes : Set (Ideal R) :=
  Ideal.minimalPrimes ⊥

lemma minimalPrimes_eq_minimals : minimalPrimes R = {x | Minimal Ideal.IsPrime x} :=
  congr_arg Minimal (by simp)

variable {I J}

theorem Ideal.nonempty_minimalPrimes (h : I ≠ ⊤) : Nonempty I.minimalPrimes := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩

theorem Ideal.eq_bot_of_minimalPrimes_eq_empty (h : I.minimalPrimes = ∅) : I = ⊤ := by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)
