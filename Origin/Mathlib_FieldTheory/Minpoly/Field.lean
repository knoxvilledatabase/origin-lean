/-
Extracted from FieldTheory/Minpoly/Field.lean
Genuine: 9 of 11 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!
# Minimal polynomials on an algebra over a field

This file specializes the theory of minpoly to the setting of field extensions
and derives some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

open Polynomial Set Function minpoly

namespace minpoly

variable {A B : Type*}

variable (A) [Field A]

section Ring

variable [Ring B] [Algebra A B] (x : B)

-- DISSOLVED: degree_le_of_ne_zero

-- DISSOLVED: ne_zero_of_finite

theorem unique {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
    (pmin : ∀ q : A[X], q.Monic → Polynomial.aeval x q = 0 → degree p ≤ degree q) :
    p = minpoly A x := by
  have hx : IsIntegral A x := ⟨p, pmonic, hp⟩
  symm; apply eq_of_sub_eq_zero
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz (by simp [hp]) |>.not_gt
  apply degree_sub_lt _ (minpoly.ne_zero hx)
  · rw [(monic hx).leadingCoeff, pmonic.leadingCoeff]
  · exact le_antisymm (min A x pmonic hp) (pmin (minpoly A x) (monic hx) (aeval A x))

theorem unique_of_degree_le_degree_minpoly {p : A[X]} (pmonic : p.Monic) (hp : p.aeval x = 0)
    (pmin : p.degree ≤ (minpoly A x).degree) : p = minpoly A x :=
  unique _ _ pmonic hp fun _ qm hq ↦ pmin.trans <| min _ _ qm hq

theorem dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A x ∣ p := by
  by_cases hp0 : p = 0
  · simp only [hp0, dvd_zero]
  have hx : IsIntegral A x := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
  rw [← modByMonic_eq_zero_iff_dvd (monic hx)]
  by_contra hnz
  apply degree_le_of_ne_zero A x hnz
    ((aeval_modByMonic_eq_self_of_root (aeval _ _)).trans hp) |>.not_gt
  exact degree_modByMonic_lt _ (monic hx)

variable {A x} in

lemma dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval x p = 0 :=
  ⟨fun ⟨q, hq⟩ ↦ by rw [hq, map_mul, aeval, zero_mul], minpoly.dvd A x⟩

theorem isRadical [IsReduced B] : IsRadical (minpoly A x) := fun n p dvd ↦ by
  rw [dvd_iff] at dvd ⊢; rw [map_pow] at dvd; exact IsReduced.eq_zero _ ⟨n, dvd⟩

theorem dvd_map_of_isScalarTower (A K : Type*) {R : Type*} [CommRing A] [Field K] [Ring R]
    [Algebra A K] [Algebra A R] [Algebra K R] [IsScalarTower A K R] (x : R) :
    minpoly K x ∣ (minpoly A x).map (algebraMap A K) := by
  refine minpoly.dvd K x ?_
  rw [aeval_map_algebraMap, minpoly.aeval]

theorem dvd_map_of_isScalarTower' (R : Type*) {S : Type*} (K L : Type*) [CommRing R]
    [CommRing S] [Field K] [Ring L] [Algebra R S] [Algebra R K] [Algebra S L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] (s : S) :
    minpoly K (algebraMap S L s) ∣ map (algebraMap R K) (minpoly R s) := by
  apply minpoly.dvd K (algebraMap S L s)
  rw [← map_aeval_eq_aeval_map, minpoly.aeval, map_zero]
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem aeval_of_isScalarTower (R : Type*) {K T U : Type*} [CommRing R] [Field K] [CommRing T]
    [Algebra R K] [Algebra K T] [Algebra R T] [IsScalarTower R K T] [CommSemiring U] [Algebra K U]
    [Algebra R U] [IsScalarTower R K U] (x : T) (y : U)
    (hy : Polynomial.aeval y (minpoly K x) = 0) : Polynomial.aeval y (minpoly R x) = 0 :=
  aeval_map_algebraMap K y (minpoly R x) ▸
    eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebraMap K U) y
      (minpoly.dvd_map_of_isScalarTower R K x) hy

theorem map_algebraMap {F E A : Type*} [Field F] [Field E] [CommRing A]
    [Algebra F E] [Algebra E A] [Algebra F A] [IsScalarTower F E A]
    {a : A} (ha : IsIntegral F a) (h : minpoly E a ∈ lifts (algebraMap F E)) :
    (minpoly F a).map (algebraMap F E) = minpoly E a := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.tower_top)
    ((algebraMap F E).injective.monic_map_iff.mp <| minpoly.monic ha)
    (minpoly.dvd E a (by simp)) ?_
  obtain ⟨g, hg, hgdeg, hgmon⟩ := lifts_and_natDegree_eq_and_monic h (minpoly.monic ha.tower_top)
  rw [natDegree_map, ← hgdeg]
  refine natDegree_le_of_dvd (minpoly.dvd F a ?_) hgmon.ne_zero
  rw [← aeval_map_algebraMap A, IsScalarTower.algebraMap_eq F E A, ← coe_mapRingHom,
    ← mapRingHom_comp, RingHom.comp_apply, coe_mapRingHom, coe_mapRingHom, hg,
    aeval_map_algebraMap, minpoly.aeval]
