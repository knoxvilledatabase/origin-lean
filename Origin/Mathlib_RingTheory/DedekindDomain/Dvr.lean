/-
Extracted from RingTheory/DedekindDomain/Dvr.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at every nonzero prime ideal is a DVR.

## Main definitions

- `IsDedekindDomainDvr` alternatively defines a Dedekind domain as an integral domain that
  is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` shows that
  `IsDedekindDomain` implies the localization at each nonzero prime ideal is a DVR.
- `IsDedekindDomain.isDedekindDomainDvr` is one direction of the equivalence of definitions
  of a Dedekind domain

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (A : Type*) [CommRing A] [IsDomain A]

open scoped nonZeroDivisors Polynomial

class IsDedekindDomainDvr : Prop extends IsNoetherian A A where
  is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : Ideal A), ∀ _ : P.IsPrime,
    IsDiscreteValuationRing (Localization.AtPrime P)

theorem Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
    [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (hM : M ≤ R⁰)
    [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ := ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) p) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨p, hpp⟩).2.1
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) P) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨P, hPm.isPrime⟩).2.1
  have hlt : Ideal.comap (algebraMap R Rₘ) p < Ideal.comap (algebraMap R Rₘ) P := hpP'
  refine h.not_lt_lt ⊥ (Ideal.comap _ _) (Ideal.comap _ _) ⟨?_, hlt⟩
  exact IsLocalization.bot_lt_comap_prime _ _ hM _ hp0⟩

theorem IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM : M ≤ A⁰)
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  have h : ∀ y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  letI : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  haveI : IsScalarTower A Aₘ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq h x).symm
  haveI : IsFractionRing Aₘ (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M _ _
  refine (isDedekindDomain_iff _ (FractionRing A)).mpr ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact IsLocalization.isNoetherianRing M _ inferInstance
  · exact Ring.DimensionLEOne.localization Aₘ hM
  · intro x hx
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp IsDedekindRing.toIsIntegralClosure hy
    refine ⟨IsLocalization.mk' Aₘ z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
    rw [hz, ← Algebra.smul_def]
    rfl

theorem IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ

-- INSTANCE (free from Core): Localization.AtPrime.isDedekindDomain

theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsDiscreteValuationRing Aₘ := by
  classical
  letI : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  letI : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mpr
      (IsLocalization.AtPrime.isDedekindDomain A P _)

-- INSTANCE (free from Core): IsDedekindDomain.isDedekindDomainDvr

-- INSTANCE (free from Core): IsDedekindDomainDvr.ring_dimensionLEOne

-- INSTANCE (free from Core): IsDedekindDomainDvr.isIntegrallyClosed

-- INSTANCE (free from Core): IsDedekindDomainDvr.isDedekindDomain
