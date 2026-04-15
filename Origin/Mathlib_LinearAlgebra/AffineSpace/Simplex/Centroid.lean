/-
Extracted from LinearAlgebra/AffineSpace/Simplex/Centroid.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Centroid of a simplex in affine space

This file proves some basic properties of the centroid of a simplex in affine space.
The definition of the centroid is based on `Finset.univ.centroid` applied to the set of vertices.
For convenience, we use `Simplex.centroid` as an abbreviation.

This file also defines `faceOppositeCentroid`, which is the centroid of the facet of the simplex
obtained by removing one vertex.

We prove several relations among the `centroid`, the `faceOppositeCentroid`, and the vertices of
the simplex. In particular, we prove a version of Commandino's theorem in arbitrary dimensions:
the centroid lies on each median, dividing it in a ratio of `n : 1`, where `n` is the dimension
of the simplex.

## Main definitions

* `centroid` is the centroid of a simplex, defined via `Finset.univ.centroid` on its vertices.

* `faceOppositeCentroid` is the centroid of the facet obtained by removing one vertex from the
  simplex.

* `median` is the line connecting a vertex to the corresponding faceOppositeCentroid.

* `medial` is the simplex formed by all `faceOppositeCentroid`.

## References

* https://en.wikipedia.org/wiki/Median_(geometry)
* https://en.wikipedia.org/wiki/Commandino%27s_theorem

-/

noncomputable section

open Finset AffineSubspace

namespace Affine

namespace Simplex

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {n : ℕ}

abbrev centroid (t : Affine.Simplex k P n) : P := Finset.univ.centroid k t.points

theorem centroid_mem_affineSpan [CharZero k] {n : ℕ} (s : Simplex k P n) :
    s.centroid ∈ affineSpan k (Set.range s.points) :=
  centroid_mem_affineSpan_of_card_eq_add_one k _ (card_fin (n + 1))

theorem centroid_notMem_affineSpan_of_ne_univ [CharZero k] (s : Simplex k P n)
    {t : Set (Fin (n + 1))} (ht : t ≠ Set.univ) :
    s.centroid ∉ affineSpan k (s.points '' t) := by
  intro h
  have hssubset : t ⊂ Set.univ := by grind
  obtain ⟨i, hi⟩ := Set.exists_of_ssubset hssubset
  rw [s.centroid_eq_affineCombination] at h
  set w := (centroidWeights k (univ : Finset (Fin (n + 1)))) with wdef
  have hw : ∑ i, w i = 1 := by rw [sum_centroidWeights_eq_one_of_nonempty _ _ (by simp)]
  have h1 := AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan s.independent hw h
    (by simp) hi.2
  have h2 : w i = (1 : k) / (n + 1) := by
    simp [wdef, centroidWeights_apply, card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
  simp only [h2, one_div, inv_eq_zero] at h1
  norm_cast at h1

theorem centroid_vsub_eq {n : ℕ} [CharZero k] (s : Simplex k P n) (p : P) :
    s.centroid -ᵥ p = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ p) := by
  rw [centroid_vsub_const _ _ (by simp), centroid_def, affineCombination_eq_linear_combination
    (hw := sum_centroidWeights_eq_one_of_nonempty _ _ (by simp))]
  simp [smul_sum]

theorem centroid_eq_smul_sum_vsub_vadd [CharZero k] (s : Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n + 1 : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) +ᵥ s.points i := by
  rw [← s.centroid_vsub_eq, vsub_vadd]

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [centroid_eq_smul_sum_vsub_vadd s i, vadd_vsub, smul_smul, mul_inv_cancel₀, one_smul]
  norm_cast

theorem centroid_weighted_vsub_eq_zero [CharZero k] (s : Simplex k P n) :
    ∑ i, (s.points i -ᵥ s.centroid) = 0 := by
  have h := centroid_vsub_eq s s.centroid
  simp only [vsub_self] at h
  symm at h
  rw [smul_eq_zero_iff_right (inv_ne_zero (by norm_cast))] at h
  exact h

theorem eq_centroid_iff_sum_vsub_eq_zero [CharZero k] {s : Simplex k P n} {p : P} :
    p = s.centroid ↔ ∑ i, (s.points i -ᵥ p) = 0 := by
  constructor
  · intro h
    rw [h, centroid_weighted_vsub_eq_zero]
  · intro h
    rw [← vsub_eq_zero_iff_eq]
    have : ∑ i, (s.points i -ᵥ p) = ∑ i, ((s.points i -ᵥ s.centroid) - (p -ᵥ s.centroid)) := by
      apply sum_congr rfl
      intro x hx
      rw [vsub_sub_vsub_cancel_right _ _ s.centroid]
    rw [this, sum_sub_distrib, centroid_weighted_vsub_eq_zero] at h
    simp only [sum_const, card_univ, Fintype.card_fin, zero_sub, neg_eq_zero] at h
    have h' : ((n : k) + 1) • (p -ᵥ s.centroid) = 0 := by norm_cast
    rw [smul_eq_zero_iff_right (by norm_cast)] at h'
    exact h'

theorem face_centroid_eq_centroid {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : #fs = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points := by
  convert (Finset.univ.centroid_map k (fs.orderEmbOfFin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp
