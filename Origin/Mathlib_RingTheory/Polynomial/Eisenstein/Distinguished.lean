/-
Extracted from RingTheory/Polynomial/Eisenstein/Distinguished.lean
Genuine: 4 of 6 | Dissolved: 2 | Infrastructure: 0
-/
import Origin.Core

/-!

# Distinguished polynomial

In this file we define the predicate `Polynomial.IsDistinguishedAt`
and develop the most basic lemmas about it.

-/

open scoped Polynomial

open PowerSeries Ideal Quotient

variable {R : Type*} [CommRing R]

structure Polynomial.IsDistinguishedAt (f : R[X]) (I : Ideal R) : Prop
    extends f.IsWeaklyEisensteinAt I where
  monic : f.Monic

namespace Polynomial.IsDistinguishedAt

lemma mul {f f' : R[X]} {I : Ideal R} (hf : f.IsDistinguishedAt I) (hf' : f'.IsDistinguishedAt I) :
    (f * f').IsDistinguishedAt I :=
  ⟨hf.toIsWeaklyEisensteinAt.mul hf'.toIsWeaklyEisensteinAt, hf.monic.mul hf'.monic⟩

lemma map_eq_X_pow {f : R[X]} {I : Ideal R} (distinguish : f.IsDistinguishedAt I) :
    f.map (Ideal.Quotient.mk I) = Polynomial.X ^ f.natDegree := by
  ext i
  by_cases ne : i = f.natDegree
  · simp [ne, distinguish.monic]
  · rcases lt_or_gt_of_ne ne with lt | gt
    · simpa [ne, eq_zero_iff_mem] using (distinguish.mem lt)
    · simp [ne, Polynomial.coeff_eq_zero_of_natDegree_lt gt]

section degree_eq_order_map

variable {I : Ideal R} (f h : R⟦X⟧) {g : R[X]}

-- DISSOLVED: map_ne_zero_of_eq_mul

-- DISSOLVED: degree_eq_coe_lift_order_map

lemma coe_natDegree_eq_order_map (distinguish : g.IsDistinguishedAt I)
    (notMem : PowerSeries.constantCoeff h ∉ I) (eq : f = g * h) :
    g.natDegree = (f.map (Ideal.Quotient.mk I)).order := by
  rw [natDegree, distinguish.degree_eq_coe_lift_order_map f h notMem eq]
  exact ENat.coe_lift _ <| order_finite_iff_ne_zero.2 <|
    distinguish.map_ne_zero_of_eq_mul f h notMem eq

end degree_eq_order_map

end Polynomial.IsDistinguishedAt
