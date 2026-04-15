/-
Extracted from RingTheory/UniqueFactorizationDomain/ClassGroup.lean
Genuine: 2 of 4 | Dissolved: 1 | Infrastructure: 1
-/
import Origin.Core

/-!
# The class group of a Unique Factorization Domain is trivial
This file proves that the ideal class group of a Normalized GCD Domain is trivial.
The main application is to Unique Factorization Domains,
which are known to be Normalized GCD Domains.

## Main result
- `NormalizedGCDMonoid.subsingleton_classGroup` : the class group of a domain with
  normalizable gcd is trivial. This includes unique factorization domains.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

open scoped nonZeroDivisors

open FractionalIdeal Ideal

variable {R : Type*} [CommRing R] [IsDomain R] [Nonempty (NormalizedGCDMonoid R)]

namespace NormalizedGCDMonoid

-- DISSOLVED: isPrincipal_of_exists_mul_ne_zero_isPrincipal

private theorem isPrincipal_of_isUnit_fractionalIdeal (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨a, K, ha0, h⟩ := exists_eq_spanSingleton_mul (I : FractionalIdeal R⁰ (FractionRing R))⁻¹
  have hIK : I * K = Ideal.span ({a} : Set R) :=
    (coeIdeal_inj (K := FractionRing R)).mp <| by
      rw [coeIdeal_mul, coeIdeal_span_singleton]
      rw [← mul_inv_cancel_iff_isUnit] at hI
      have ha0' := spanSingleton_mul_inv (R₁ := R) (FractionRing R)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr ha0))
      replace h :=
        congrArg
          (fun t =>
            spanSingleton R⁰ ((algebraMap R (FractionRing R)) a) * I * t)
          h.symm
      dsimp only at h
      rwa [mul_mul_mul_comm, ← spanSingleton_inv, ha0', one_mul, mul_assoc, hI, mul_one] at h
  refine isPrincipal_of_exists_mul_ne_zero_isPrincipal (J := I) ?_
  refine ⟨K, ?_, ?_⟩
  · simp [hIK, ha0]
  · simpa [hIK] using (inferInstance : (Ideal.span {a}).IsPrincipal)

private theorem isPrincipal_fractionalIdeal_of_isUnit
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (I : Submodule R (FractionRing R)).IsPrincipal := by
  let J : Ideal R := (I : FractionalIdeal R⁰ (FractionRing R)).num
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) :=
    FractionalIdeal.isUnit_num.mpr ⟨I, rfl⟩
  have hJprin : J.IsPrincipal := isPrincipal_of_isUnit_fractionalIdeal J hJunit
  exact isPrincipal_of_isPrincipal_num
    (I : FractionalIdeal R⁰ (FractionRing R)) hJprin

-- INSTANCE (free from Core): subsingleton_classGroup

end NormalizedGCDMonoid
