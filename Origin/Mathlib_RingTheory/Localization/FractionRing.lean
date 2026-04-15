/-
Extracted from RingTheory/Localization/FractionRing.lean
Genuine: 14 of 19 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Fraction ring / fraction field Frac(R) as localization

## Main definitions

* `IsFractionRing R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
  `IsLocalization (NonZeroDivisors R) K`

## Main results

* `IsFractionRing.field`: a definition (not an instance) stating the localization of an integral
  domain `R` at `R \ {0}` is a field
* `Rat.isFractionRing` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

assert_not_exists Ideal

open nonZeroDivisors

variable (R : Type*) [CommRing R] {M : Submonoid R} (S : Type*) [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

variable {A : Type*} [CommRing A] (K : Type*)

abbrev IsFractionRing (R : Type*) [CommSemiring R] (K : Type*) [CommSemiring K] [Algebra R K] :=
  IsLocalization (nonZeroDivisors R) K

-- INSTANCE (free from Core): {R

theorem IsFractionRing.of_algEquiv {R : Type*} [CommSemiring R] {K L : Type*}
    [CommSemiring K] [Algebra R K] [CommSemiring L] [Algebra R L] [h : IsFractionRing R K]
    (e : K ≃ₐ[R] L) :
    IsFractionRing R L := IsLocalization.isLocalization_of_algEquiv _ e

-- INSTANCE (free from Core): Rat.isFractionRing

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): NNRat.isFractionRing

namespace IsFractionRing

open IsLocalization

theorem of_field [Field K] [Algebra R K] [FaithfulSMul R K]
    (surj : ∀ z : K, ∃ x y, z = algebraMap R K x / algebraMap R K y) :
    IsFractionRing R K :=
  have inj := FaithfulSMul.algebraMap_injective R K
  have := inj.noZeroDivisors _ (map_zero _) (map_mul _)
  have := Module.nontrivial R K

{ map_units x :=

    .mk0 _ <| (map_ne_zero_iff _ inj).mpr <| mem_nonZeroDivisors_iff_ne_zero.mp x.2

  surj z := by

    have ⟨x, y, eq⟩ := surj z

    obtain rfl | hy := eq_or_ne y 0

    · obtain rfl : z = 0 := by simpa using eq

      exact ⟨(0, 1), by simp⟩

    exact ⟨⟨x, y, mem_nonZeroDivisors_iff_ne_zero.mpr hy⟩,

      (eq_div_iff_mul_eq <| (map_ne_zero_iff _ inj).mpr hy).mp eq⟩

  exists_of_eq eq := ⟨1, by simpa using inj eq⟩ }

variable {R K}

section CommSemiring

theorem of_ringEquiv_left {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
    {K : Type*} [CommSemiring K] [Algebra R K] (e : R ≃+* S) [Algebra S K]
    (h : ∀ x, algebraMap R K x = algebraMap S K (e x)) [IsFractionRing S K] :
    IsFractionRing R K := IsLocalization.of_ringEquiv_left e (MulEquivClass.map_nonZeroDivisors e) h

end CommSemiring

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

theorem to_map_eq_zero_iff {x : R} : algebraMap R K x = 0 ↔ x = 0 :=
  IsLocalization.to_map_eq_zero_iff _ le_rfl

variable (R K)

protected theorem injective : Function.Injective (algebraMap R K) :=
  IsLocalization.injective _ (le_of_eq rfl)

include R in

theorem nonZeroDivisors_eq_isUnit : K⁰ = IsUnit.submonoid K := by
  refine le_antisymm (fun x hx ↦ ?_) (isUnit_le_nonZeroDivisors K)
  have ⟨r, eq⟩ := surj R⁰ x
  let r' : R⁰ := ⟨r.1, mem_nonZeroDivisors_of_injective (IsFractionRing.injective R K)
    (eq ▸ mul_mem hx (map_units ..).mem_nonZeroDivisors)⟩
  exact isUnit_of_mul_isUnit_left <| eq ▸ map_units K r'

include R in

noncomputable def algEquiv (L) [CommRing L] [Algebra K L] [IsFractionRing K L] : K ≃ₐ[K] L :=
  atUnits K _ (nonZeroDivisors_eq_isUnit R K).le

include R in

theorem idem : IsFractionRing K K := IsLocalization.self (nonZeroDivisors_eq_isUnit R K).le

theorem trans (L) [CommRing L] [Algebra K L] [IsFractionRing K L] [Algebra R L]
    [IsScalarTower R K L] : IsFractionRing R L :=
  isLocalization_of_algEquiv _ <| (algEquiv R K L).restrictScalars R

-- INSTANCE (free from Core): (priority

variable {R}

theorem self_iff_nonZeroDivisors_eq_isUnit : IsFractionRing R R ↔ R⁰ = IsUnit.submonoid R where
  mp _ := nonZeroDivisors_eq_isUnit R R
  mpr h := IsLocalization.self h.le

theorem self_iff_nonZeroDivisors_le_isUnit : IsFractionRing R R ↔ R⁰ ≤ IsUnit.submonoid R := by
  rw [self_iff_nonZeroDivisors_eq_isUnit, le_antisymm_iff,
    and_iff_left (isUnit_le_nonZeroDivisors R)]

theorem self_iff_bijective : IsFractionRing R R ↔ Function.Bijective (algebraMap R K) where
  mp h := (atUnits R _ <| self_iff_nonZeroDivisors_le_isUnit.mp h).bijective
  mpr h := isLocalization_of_algEquiv _ (AlgEquiv.ofBijective (Algebra.ofId R K) h).symm

theorem self_iff_surjective : IsFractionRing R R ↔ Function.Surjective (algebraMap R K) := by
  rw [self_iff_bijective K, Function.Bijective, and_iff_right (IsFractionRing.injective R K)]

variable {K}

open algebraMap in
