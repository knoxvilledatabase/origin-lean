/-
Extracted from NumberTheory/Padics/HeightOneSpectrum.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Isomorphisms between `adicCompletion ℚ` and `ℚ_[p]`

Let `R` have field of fractions `ℚ`. If `v : HeightOneSpectrum R`, then `v.adicCompletion ℚ` is
the uniform space completion of `ℚ` with respect to the `v`-adic valuation.
On the other hand, `ℚ_[p]` is the `p`-adic numbers, defined as the completion of `ℚ` with respect
to the `p`-adic norm using the completion of Cauchy sequences. This file constructs continuous
`ℚ`-algebra isomorphisms between the two, as well as continuous `ℤ`-algebra isomorphisms for their
respective rings of integers.

Isomorphisms are provided in both directions, allowing traversal of the following diagram:
```
HeightOneSpectrum R <----------->  Nat.Primes
          |                               |
          |                               |
          v                               v
v.adicCompletionIntegers ℚ  <------->   ℤ_[p]
          |                               |
          |                               |
          v                               v
v.adicCompletion ℚ  <--------------->   ℚ_[p]
```

## Main definitions
- `Rat.HeightOneSpectrum.primesEquiv` : the equivalence between height-one prime ideals of
  `R` and prime numbers in `ℕ`.
- `Rat.HeightOneSpectrum.padicEquiv v` : the continuous `ℚ`-algebra isomorphism
  `v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`.
- `Padic.adicCompletionEquiv p` : the continuous `ℚ`-algebra isomorphism
  `ℚ_[p] ≃A[ℚ] (primesEquiv.symm p).adicCompletion ℚ`.
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v` : the continuous `ℤ`-algebra
  isomorphism `v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[natGenerator v]`.
- `PadicInt.adicCompletionIntegersEquiv p` : the continuous `ℤ`-algebra isomorphism
  `ℤ_[p] ≃A[ℤ] (primesEquiv.symm p).adicCompletionIntegers ℚ`.

TODO : Abstract the isomorphisms in this file using a universal predicate on adic completions,
along the lines of `IsComplete` + uniformity arises from a valuation + the valuations are
equivalent. It is best to do this after `Valued` has been refactored, or at least after
`adicCompletion` has `IsValuativeTopology` instance.
-/

open IsDedekindDomain UniformSpace.Completion NumberField PadicInt

-- INSTANCE (free from Core): (p

variable (R : Type*) [CommRing R] [Algebra R ℚ]

theorem Rat.int_algebraMap_injective : Function.Injective (algebraMap ℤ R) :=
  .of_comp (IsScalarTower.algebraMap_eq ℤ R ℚ ▸ RingHom.injective_int (algebraMap ℤ ℚ))

variable [IsIntegralClosure R ℤ ℚ]

theorem Rat.int_algebraMap_surjective [IsFractionRing R ℚ] :
    Function.Surjective (algebraMap ℤ R) := by
  intro x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 <|
    IsIntegral.algebraMap (B := ℚ) (IsIntegralClosure.isIntegral ℤ ℚ x)
  exact ⟨y, IsFractionRing.injective R ℚ <| by simp only [← IsScalarTower.algebraMap_apply, hy]⟩

noncomputable def Rat.IsIntegralClosure.intEquiv : R ≃+* ℤ :=
  (NumberField.RingOfIntegers.equiv R).symm.trans ringOfIntegersEquiv
