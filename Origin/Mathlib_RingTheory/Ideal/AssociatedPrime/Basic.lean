/-
Extracted from RingTheory/Ideal/AssociatedPrime/Basic.lean
Genuine: 7 of 9 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  radical of the annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a Noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a Noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## Implementation details

The presence of the radical in the definition of `IsAssociatedPrime` is slightly nonstandard but
gives the correct characterization of the prime ideals of any minimal primary decomposition in the
non-Noetherian setting (see Theorem 4.5 in Atiyah-Macdonald). If the ring `R` is assumed to be
Noetherian, then the radical can be dropped from the definition (see `isAssociatedPrime_iff`).

See also [Stacks: Lemma 0566](https://stacks.math.columbia.edu/tag/0566) which states that a
prime `p` is minimal among primes containing an annihilator an element of `M` if and only if
`p R_p` is an associated prime of `M_p` (including the radical).

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
-/

open LinearMap Submodule

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M)
  (I : Ideal R) (x : M)

protected structure IsAssociatedPrime : Prop extends I.IsPrime where
  eq_radical_colon : ∃ x, I = (colon N {x}).radical

protected def associatedPrimes : Set (Ideal R) :=
  { I | N.IsAssociatedPrime I }

variable {N I}

protected theorem isAssociatedPrime_def :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = (colon N {x}).radical :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

protected theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = colon N {x} := by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes (x := x) ?_⟩
    rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩

-- INSTANCE (free from Core): (I

protected theorem AssociatePrimes.mem_iff : I ∈ N.associatedPrimes ↔ N.IsAssociatedPrime I :=
  .rfl

end Submodule

section Semiring

variable {R : Type*} [CommSemiring R] (I J : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M]

def IsAssociatedPrime : Prop :=
  (⊥ : Submodule R M).IsAssociatedPrime I

variable (R) in

def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M} {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')
