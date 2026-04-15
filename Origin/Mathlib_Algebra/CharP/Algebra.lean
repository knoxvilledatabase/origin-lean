/-
Extracted from Algebra/CharP/Algebra.lean
Genuine: 16 of 27 | Dissolved: 5 | Infrastructure: 6
-/
import Origin.Core

/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of free algebras over `R`
and the fraction field `FractionRing R`.


## Main results

- `charP_of_injective_algebraMap` If `R →+* A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances constructed from this result:
- Any `FreeAlgebra R X` has the same characteristic as `R`.
- The `FractionRing R` of an integral domain `R` has the same characteristic as `R`.

-/

variable {R A : Type*}

theorem CharP.dvd_of_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (p q : ℕ) [CharP R p] [CharP A q] : q ∣ p := by
  refine (CharP.cast_eq_zero_iff A q p).mp ?_
  rw [← map_natCast f p, CharP.cast_eq_zero, map_zero]

-- DISSOLVED: CharP.of_ringHom_of_ne_zero

theorem charP_of_injective_ringHom [NonAssocSemiring R] [NonAssocSemiring A]
    {f : R →+* A} (h : Function.Injective f) (p : ℕ) [CharP R p] : CharP A p where
  cast_eq_zero_iff x := by
    rw [← CharP.cast_eq_zero_iff R p x, ← map_natCast f x, map_eq_zero_iff f h]

theorem charP_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom h p

theorem charP_of_injective_algebraMap' (R : Type*) [CommRing R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] (p : ℕ) [CharP R p] : CharP A p :=
  charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

-- DISSOLVED: charZero_of_injective_ringHom

-- DISSOLVED: charZero_of_injective_algebraMap

theorem RingHom.charP [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [CharP A p] : CharP R p := by
  obtain ⟨q, h⟩ := CharP.exists R
  exact CharP.eq _ (charP_of_injective_ringHom H q) ‹CharP A p› ▸ h

protected theorem RingHom.charP_iff [NonAssocSemiring R] [NonAssocSemiring A]
    (f : R →+* A) (H : Function.Injective f) (p : ℕ) : CharP R p ↔ CharP A p :=
  ⟨fun _ ↦ charP_of_injective_ringHom H p, fun _ ↦ f.charP H p⟩

lemma expChar_of_injective_ringHom
    [NonAssocSemiring R] [NonAssocSemiring A] {f : R →+* A} (h : Function.Injective f)
    (q : ℕ) [hR : ExpChar R q] : ExpChar A q := by
  rcases hR with _ | hprime
  · haveI := charZero_of_injective_ringHom h; exact .zero
  haveI := charP_of_injective_ringHom h q; exact .prime hprime

lemma RingHom.expChar [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) [ExpChar A p] : ExpChar R p := by
  cases ‹ExpChar A p› with
  | zero => haveI := f.charZero; exact .zero
  | prime hp => haveI := f.charP H p; exact .prime hp

lemma RingHom.expChar_iff [NonAssocSemiring R] [NonAssocSemiring A] (f : R →+* A)
    (H : Function.Injective f) (p : ℕ) : ExpChar R p ↔ ExpChar A p :=
  ⟨fun _ ↦ expChar_of_injective_ringHom H p, fun _ ↦ f.expChar H p⟩

lemma expChar_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom h q

variable (R) in

theorem ExpChar.of_injective_algebraMap' [CommRing R] [CommRing A]
    [Algebra R A] [FaithfulSMul R A] (q : ℕ) [ExpChar R q] : ExpChar A q :=
  expChar_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) q

namespace Subfield

variable [DivisionRing R] (L : Subfield R) (p : ℕ)

-- INSTANCE (free from Core): charP

-- INSTANCE (free from Core): expChar

end Subfield

/-!
As an application, a `ℚ`-algebra has characteristic zero.
-/

section QAlgebra

variable (R : Type*) [Nontrivial R]

theorem algebraRat.charP_zero [Semiring R] [Algebra ℚ R] : CharP R 0 :=
  charP_of_injective_algebraMap (algebraMap ℚ R).injective 0

-- DISSOLVED: algebraRat.charZero

end QAlgebra

/-!
An algebra over a field has the same characteristic as the field.
-/

lemma RingHom.charP_iff_charP {K L : Type*} [DivisionRing K] [NonAssocSemiring L] [Nontrivial L]
    (f : K →+* L) (p : ℕ) : CharP K p ↔ CharP L p := by
  simp only [charP_iff, ← f.injective.eq_iff, map_natCast f, map_zero f]

variable (K L : Type*) [Field K] [CommSemiring L] [Nontrivial L] [Algebra K L]

protected theorem Algebra.charP_iff (p : ℕ) : CharP K p ↔ CharP L p :=
  (algebraMap K L).charP_iff_charP p

theorem Algebra.ringChar_eq : ringChar K = ringChar L := by
  rw [ringChar.eq_iff, Algebra.charP_iff K L]
  apply ringChar.charP

end

namespace FreeAlgebra

variable {R X : Type*} [CommSemiring R] (p : ℕ)

-- INSTANCE (free from Core): charP

-- INSTANCE (free from Core): charZero

end FreeAlgebra

namespace IsFractionRing

variable (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (p : ℕ)

theorem charP_of_isFractionRing [CharP R p] : CharP K p :=
  charP_of_injective_algebraMap (IsFractionRing.injective R K) p

-- DISSOLVED: charZero_of_isFractionRing

variable [IsDomain R]

-- INSTANCE (free from Core): charP

-- INSTANCE (free from Core): charZero

end IsFractionRing
