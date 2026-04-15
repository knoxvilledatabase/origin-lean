/-
Extracted from RingTheory/DedekindDomain/Basic.lean
Genuine: 11 of 16 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Dedekind rings and domains

This file defines the notion of a Dedekind ring (domain),
as a Noetherian integrally closed commutative ring (domain) of Krull dimension at most one.

## Main definitions

- `IsDedekindRing` defines a Dedekind ring as a commutative ring that is
  Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
  `isDedekindRing_iff` shows that this does not depend on the choice of field of fractions.
- `IsDedekindDomain` defines a Dedekind domain as a Dedekind ring that is a domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.

Often, definitions assume that Dedekind rings are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

class Ring.DimensionLEOne : Prop where
  (maximalOfPrime : ∀ {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal)

open Ideal Ring

theorem Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R]
    {p : Ideal R} (h : p.IsPrime) (hp : p ≠ ⊥) : p.IsMaximal :=
  DimensionLEOne.maximalOfPrime hp h

namespace Ring.DimensionLEOne

-- INSTANCE (free from Core): principal_ideal_ring

theorem isIntegralClosure (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R] [Algebra R A]
    [Algebra R B] [Algebra B A] [IsScalarTower R B A] [IsIntegralClosure B R A] [DimensionLEOne R] :
    DimensionLEOne B where
  maximalOfPrime := fun {p} ne_bot _ =>
    IsIntegralClosure.isMaximal_of_isMaximal_comap (R := R) A p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegralClosure.comap_ne_bot A ne_bot))

-- INSTANCE (free from Core): integralClosure

variable {R}

theorem not_lt_lt [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.ne ((hp₁.isMaximal (bot_le.trans_lt h01).ne').eq_of_le hp₂.ne_top h12.le)

theorem eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrime] (hpP : p < P) :
    p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

variable {A} in

theorem of_ringEquiv [hA : Ring.DimensionLEOne A] (e : R ≃+* A) : Ring.DimensionLEOne R where
  maximalOfPrime {P} hP_ne hP_prime := by
    rw [← Ideal.map_comap_eq_self_of_equiv e.symm P,
      Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective]
    apply Ring.DimensionLEOne.maximalOfPrime ?_ (P.comap_isPrime e.symm)
    simp [Ideal.map_eq_bot_iff_of_injective e.injective, hP_ne]

end Ring.DimensionLEOne

class IsDedekindRing : Prop
  extends IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A)

theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

class IsDedekindDomain : Prop
  extends IsDomain A, IsDedekindRing A

-- INSTANCE (free from Core): 90]

-- INSTANCE (free from Core): [IsDomain

theorem isDedekindDomain_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

-- INSTANCE (free from Core): (priority

variable {R} in

theorem IsLocalRing.primesOver_eq [IsLocalRing A] [IsDedekindDomain A] [Algebra R A]
    [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Ideal.primesOver p A = {IsLocalRing.maximalIdeal A} := by
  have : IsDomain R := .of_faithfulSMul R A
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP ↦ ?_⟩
  · obtain ⟨w', hmax, hover⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := A) p
    exact ⟨w', hmax.isPrime, hover⟩
  · exact IsLocalRing.eq_maximalIdeal <| hP.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 hP)
