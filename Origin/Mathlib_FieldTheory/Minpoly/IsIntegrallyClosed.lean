/-
Extracted from FieldTheory/Minpoly/IsIntegrallyClosed.lean
Genuine: 11 of 14 | Dissolved: 3 | Infrastructure: 0
-/
import Origin.Core

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

* `minpoly.isIntegrallyClosed_eq_field_fractions`: For integrally closed domains, the minimal
  polynomial over the ring is the same as the minimal polynomial over the fraction field.

* `minpoly.isIntegrallyClosed_dvd`: For integrally closed domains, the minimal polynomial divides
  any primitive polynomial that has the integral element as root.

* `IsIntegrallyClosed.Minpoly.unique`: The minimal polynomial of an element `x` is uniquely
  characterized by its defining property: if there is another monic polynomial of minimal degree
  that has `x` as a root, then this polynomial is equal to the minimal polynomial of `x`.

-/

open Polynomial Set Function minpoly Module

namespace minpoly

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]

variable (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K] [CommRing L] [Nontrivial L]
  [Algebra R L] [Algebra S L] [Algebra K L] [IsScalarTower R K L] [IsScalarTower R S L]

variable [IsIntegrallyClosed R]

theorem isIntegrallyClosed_eq_field_fractions [IsDomain S] {s : S} (hs : IsIntegral R s) :
    minpoly K (algebraMap S L s) = (minpoly R s).map (algebraMap R K) := by
  refine (eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · exact ((monic hs).irreducible_iff_irreducible_map_fraction_map).1 (irreducible hs)
  · rw [aeval_map_algebraMap, aeval_algebraMap_apply, aeval, map_zero]
  · exact (monic hs).map _

theorem isIntegrallyClosed_eq_field_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S]
    {s : S} (hs : IsIntegral R s) : minpoly K s = (minpoly R s).map (algebraMap R K) := by
  let L := FractionRing S
  rw [← isIntegrallyClosed_eq_field_fractions K L hs, algebraMap_eq (IsFractionRing.injective S L)]

end

variable [IsIntegrallyClosed R] [IsDomain S] [IsTorsionFree R S]

theorem isIntegrallyClosed_dvd {s : S} (hs : IsIntegral R s) {p : R[X]}
    (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := FractionRing S
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  have : minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (p %ₘ minpoly R s) := by
    rw [map_modByMonic _ (minpoly.monic hs), modByMonic_eq_sub_mul_div]
    refine dvd_sub (minpoly.dvd K (algebraMap S L s) ?_) ?_
    · rw [← map_aeval_eq_aeval_map, hp, map_zero]
      rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    apply dvd_mul_of_dvd_left
    rw [isIntegrallyClosed_eq_field_fractions K L hs]
  rw [isIntegrallyClosed_eq_field_fractions _ _ hs,
    map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (minpoly.monic hs)] at this
  rw [← modByMonic_eq_zero_iff_dvd (minpoly.monic hs)]
  exact Polynomial.eq_zero_of_dvd_of_degree_lt this (degree_modByMonic_lt p <| minpoly.monic hs)

theorem isIntegrallyClosed_dvd_iff {s : S} (hs : IsIntegral R s) (p : R[X]) :
    Polynomial.aeval s p = 0 ↔ minpoly R s ∣ p :=
  ⟨fun hp => isIntegrallyClosed_dvd hs hp, fun hp => by
    simpa only [RingHom.mem_ker, RingHom.coe_comp, coe_evalRingHom, coe_mapRingHom,
      Function.comp_apply, eval_map_algebraMap] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hp (minpoly.aeval R s)⟩

theorem ker_eval {s : S} (hs : IsIntegral R s) :
    RingHom.ker ((Polynomial.aeval s).toRingHom : R[X] →+* S) =
    Ideal.span ({minpoly R s} : Set R[X]) := by
  ext p
  simp_rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    isIntegrallyClosed_dvd_iff hs, ← Ideal.mem_span_singleton]

-- DISSOLVED: IsIntegrallyClosed.degree_le_of_ne_zero

theorem IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff {x : S} {p : R[X]}
    (hirr : Irreducible p) (hp : p.aeval x = 0) :
    IsIntegral R x ↔ IsUnit p.leadingCoeff where
  mp int_x := by
    obtain ⟨p, rfl⟩ := isIntegrallyClosed_dvd int_x hp
    rw [leadingCoeff_mul, monic int_x, one_mul]
    exact ((of_irreducible_mul hirr).resolve_left (not_isUnit R x)).map leadingCoeffHom
  mpr isUnit := by
    simpa [smul_smul] using (isIntegral_leadingCoeff_smul _ _ hp).smul ((isUnit.unit⁻¹ : Rˣ) : R)

theorem _root_.IsIntegrallyClosed.minpoly.unique {s : S} {P : R[X]} (hmo : P.Monic)
    (hP : Polynomial.aeval s P = 0)
    (Pmin : ∀ Q : R[X], Q.Monic → Polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
    P = minpoly R s := by
  have hs : IsIntegral R s := ⟨P, hmo, hP⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  refine IsIntegrallyClosed.degree_le_of_ne_zero (s := s) hnz (by simp [hP]) |>.not_gt ?_
  refine degree_sub_lt ?_ (ne_zero hs) ?_
  · exact le_antisymm (min R s hmo hP) (Pmin (minpoly R s) (monic hs) (aeval R s))
  · rw [(monic hs).leadingCoeff, hmo.leadingCoeff]

theorem IsIntegrallyClosed.unique_of_degree_le_degree_minpoly {s : S} {p : R[X]} (hmo : p.Monic)
    (hp : p.aeval s = 0) (pmin : p.degree ≤ (minpoly R s).degree) : p = minpoly R s :=
  IsIntegrallyClosed.minpoly.unique hmo hp fun _ qm hq ↦ pmin.trans <| min _ _ qm hq

-- DISSOLVED: IsIntegrallyClosed.isIntegral_iff_leadingCoeff_dvd

theorem prime_of_isIntegrallyClosed {x : S} (hx : IsIntegral R x) : Prime (minpoly R x) := by
  refine
    ⟨(minpoly.monic hx).ne_zero,
      ⟨fun h_contra => (ne_of_lt (minpoly.degree_pos hx)) (degree_eq_zero_of_isUnit h_contra).symm,
        fun a b h => or_iff_not_imp_left.mpr fun h' => ?_⟩⟩
  rw [← minpoly.isIntegrallyClosed_dvd_iff hx] at h' h ⊢
  rw [aeval_mul] at h
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero h' h

-- DISSOLVED: _root_.IsIntegrallyClosed.minpoly_smul

noncomputable section AdjoinRoot

open Algebra Polynomial AdjoinRoot

variable {x : S}

theorem ToAdjoin.injective (hx : IsIntegral R x) : Function.Injective (Minpoly.toAdjoin R x) := by
  refine (injective_iff_map_eq_zero _).2 fun P₁ hP₁ => ?_
  obtain ⟨P, rfl⟩ := mk_surjective P₁
  simpa [← Subalgebra.coe_eq_zero, isIntegrallyClosed_dvd_iff hx, ← aeval_def] using hP₁

def equivAdjoin (hx : IsIntegral R x) : AdjoinRoot (minpoly R x) ≃ₐ[R] adjoin R ({x} : Set S) :=
  AlgEquiv.ofBijective (Minpoly.toAdjoin R x)
    ⟨minpoly.ToAdjoin.injective hx, Minpoly.toAdjoin.surjective R x⟩
