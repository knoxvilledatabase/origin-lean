/-
Extracted from RingTheory/Localization/AtPrime/Basic.lean
Genuine: 6 of 10 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Localizations of commutative rings at the complement of a prime ideal

## Main definitions

* `IsLocalization.AtPrime (P : Ideal R) [IsPrime P] (S : Type*)` expresses that `S` is a
  localization at (the complement of) a prime ideal `P`, as an abbreviation of
  `IsLocalization P.prime_compl S`

## Main results

* `IsLocalization.AtPrime.isLocalRing`: a theorem (not an instance) stating a localization at the
  complement of a prime ideal is a local ring

## Implementation notes

See `RingTheory.Localization.Basic` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

open Module

variable {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

section AtPrime

variable (P : Ideal R) [hp : P.IsPrime]

protected abbrev IsLocalization.AtPrime :=
  IsLocalization P.primeCompl S

protected abbrev Localization.AtPrime :=
  Localization P.primeCompl

namespace IsLocalization

theorem AtPrime.nontrivial [IsLocalization.AtPrime S P] : Nontrivial S :=
  nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one, ← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t ∈ P)

theorem AtPrime.isLocalRing [IsLocalization.AtPrime S P] : IsLocalRing S :=
  letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : ∀ {r : R} {s : P.primeCompl}, mk' S r s ∈ nonunits S → r ∈ P := fun {r s} =>
        not_imp_comm.1 fun nr => isUnit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : P.primeCompl),
          mk'_mul_mk'_eq_one' _ _ <| show r ∈ P.primeCompl from nr⟩
      rcases exists_mk'_eq P.primeCompl x with ⟨rx, sx, hrx⟩
      rcases exists_mk'_eq P.primeCompl y with ⟨ry, sy, hry⟩
      rcases exists_mk'_eq P.primeCompl z with ⟨rz, sz, hrz⟩
      rw [← hrx, ← hry, ← hrz, ← mk'_add, ← mk'_mul, ← mk'_self S P.primeCompl.one_mem] at hxyz
      rw [← hrx] at hx
      rw [← hry] at hy
      obtain ⟨t, ht⟩ := IsLocalization.eq.1 hxyz
      simp only [mul_one, one_mul, Submonoid.coe_mul] at ht
      suffices (t : R) * (sx * sy * sz) ∈ P from
        not_or_intro (mt hp.mem_or_mem <| not_or_intro sx.2 sy.2) sz.2
          (hp.mem_or_mem <| (hp.mem_or_mem this).resolve_left t.2)
      rw [← ht]
      exact
        P.mul_mem_left _ <| P.mul_mem_right _ <|
            P.add_mem (P.mul_mem_right _ <| this hx) <| P.mul_mem_right _ <| this hy)

variable {A : Type*} [CommRing A] [IsDomain A]

-- INSTANCE (free from Core): isDomain_of_local_atPrime

end IsLocalization

namespace Localization

-- INSTANCE (free from Core): AtPrime.isLocalRing

-- INSTANCE (free from Core): {R

theorem _root_.IsLocalization.AtPrime.faithfulSMul (R : Type*) [CommRing R] [NoZeroDivisors R]
    [Algebra R S] (P : Ideal R) [hp : P.IsPrime] [IsLocalization.AtPrime S P] :
    FaithfulSMul R S := by
  rw [faithfulSMul_iff_algebraMap_injective, IsLocalization.injective_iff_isRegular P.primeCompl]
  exact fun ⟨_, h⟩ ↦ .of_ne_zero <| by aesop

-- INSTANCE (free from Core): {R

end Localization

end AtPrime

namespace IsLocalization

variable {A : Type*} [CommRing A] [IsDomain A]

theorem isDomain_of_atPrime (S : Type*) [CommSemiring S] [Algebra A S]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime S P] : IsDomain S :=
  isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

namespace AtPrime

variable (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]
