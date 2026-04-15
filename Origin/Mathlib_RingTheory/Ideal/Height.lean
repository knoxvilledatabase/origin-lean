/-
Extracted from RingTheory/Ideal/Height.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Height of an Ideal

In this file, we define the height of a prime ideal and the height of an ideal.

## Main definitions

* `Ideal.primeHeight` : The height of a prime ideal $\mathfrak{p}$. We define it as the supremum of
  the lengths of strictly decreasing chains of prime ideals below it. This definition is implemented
  via `Order.height`.

* `Ideal.height` : The height of an ideal. We defined it as the infimum of the `primeHeight` of the
  minimal prime ideals of I.

-/

variable {R : Type*} [CommRing R] (I : Ideal R)

open Ideal

noncomputable def Ideal.primeHeight [hI : I.IsPrime] : ℕ∞ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

noncomputable def Ideal.height : ℕ∞ :=
  ⨅ J ∈ I.minimalPrimes, @Ideal.primeHeight _ _ J (minimalPrimes_isPrime (I := I) ‹_›)

lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  unfold height primeHeight
  simp_rw [Ideal.minimalPrimes_eq_subsingleton_self]
  simp
