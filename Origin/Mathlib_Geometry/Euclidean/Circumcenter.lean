/-
Extracted from Geometry/Euclidean/Circumcenter.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

open AffineSubspace

theorem _root_.AffineIndependent.existsUnique_dist_eq {ι : Type*} [hne : Nonempty ι] [Finite ι]
    {p : ι → P} (ha : AffineIndependent ℝ p) :
    ∃! cs : Sphere P, cs.center ∈ affineSpan ℝ (Set.range p) ∧ Set.range p ⊆ (cs : Set P) := by
  cases nonempty_fintype ι
  induction hn : Fintype.card ι generalizing ι with
  | zero =>
    exfalso
    have h := Fintype.card_pos_iff.2 hne
    lia
  | succ m hm =>
    rcases m with - | m
    · rw [Fintype.card_eq_one_iff] at hn
      obtain ⟨i, hi⟩ := hn
      haveI : Unique ι := ⟨⟨i⟩, hi⟩
      use ⟨p i, 0⟩
      simp only [Set.range_unique, AffineSubspace.mem_affineSpan_singleton]
      constructor
      · simp_rw [hi default, Set.singleton_subset_iff]
        exact ⟨⟨⟩, by simp only [Metric.sphere_zero, Set.mem_singleton_iff]⟩
      · rintro ⟨cc, cr⟩
        rintro ⟨rfl, hdist⟩
        replace hdist : 0 = cr := by simpa using hdist
        rw [hi default, hdist]
    · have i := hne.some
      let ι2 := { x // x ≠ i }
      classical
      have hc : Fintype.card ι2 = m + 1 := by
        rw [Fintype.card_of_subtype {x | x ≠ i}]
        · rw [Finset.filter_not, Finset.filter_eq' _ i, if_pos (Finset.mem_univ _),
            Finset.card_sdiff, Finset.card_univ, hn]
          simp
        · simp
      haveI : Nonempty ι2 := Fintype.card_pos_iff.1 (hc.symm ▸ Nat.zero_lt_succ _)
      have ha2 : AffineIndependent ℝ fun i2 : ι2 => p i2 := ha.subtype _
      replace hm := hm ha2 _ hc
      have hr : Set.range p = insert (p i) (Set.range fun i2 : ι2 => p i2) := by
        change _ = insert _ (Set.range fun i2 : { x | x ≠ i } => p i2)
        rw [← Set.image_eq_range, ← Set.image_univ, ← Set.image_insert_eq]
        congr with j
        simp [Classical.em]
      rw [hr, ← affineSpan_insert_affineSpan]
      refine existsUnique_dist_eq_of_insert (Set.range_nonempty _) (subset_affineSpan ℝ _) ?_ hm
      convert ha.notMem_affineSpan_diff i Set.univ
      change (Set.range fun i2 : { x | x ≠ i } => p i2) = _
      rw [← Set.image_eq_range]
      congr 1 with j
      simp

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

def circumsphere {n : ℕ} (s : Simplex ℝ P n) : Sphere P :=
  s.independent.existsUnique_dist_eq.choose

theorem circumsphere_unique_dist_eq {n : ℕ} (s : Simplex ℝ P n) :
    (s.circumsphere.center ∈ affineSpan ℝ (Set.range s.points) ∧
        Set.range s.points ⊆ s.circumsphere) ∧
      ∀ cs : Sphere P,
        cs.center ∈ affineSpan ℝ (Set.range s.points) ∧ Set.range s.points ⊆ cs →
          cs = s.circumsphere :=
  s.independent.existsUnique_dist_eq.choose_spec

def circumcenter {n : ℕ} (s : Simplex ℝ P n) : P :=
  s.circumsphere.center

def circumradius {n : ℕ} (s : Simplex ℝ P n) : ℝ :=
  s.circumsphere.radius
