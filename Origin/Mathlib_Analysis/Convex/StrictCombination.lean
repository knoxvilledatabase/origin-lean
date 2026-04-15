/-
Extracted from Analysis/Convex/StrictCombination.lean
Genuine: 2 of 8 | Dissolved: 6 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex combinations in strictly convex sets and spaces.

This file proves lemmas about convex combinations of points in strictly convex sets and strictly
convex spaces.

-/

open Finset Metric

variable {R V P ι : Type*}

section Set

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [TopologicalSpace V] [AddCommGroup V]

variable [Module R V]

-- DISSOLVED: StrictConvex.centerMass_mem_interior

-- DISSOLVED: StrictConvex.sum_mem_interior

end Set

section Space

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]

-- DISSOLVED: centerMass_mem_ball_of_strictConvexSpace

-- DISSOLVED: sum_mem_ball_of_strictConvexSpace

-- DISSOLVED: norm_sum_lt_of_strictConvexSpace

variable [PseudoMetricSpace P] [NormedAddTorsor V P]

-- DISSOLVED: dist_affineCombination_lt_of_strictConvexSpace

namespace Affine

namespace Simplex

lemma dist_lt_of_mem_closedInterior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.closedInterior) (hp' : ∀ i, p ≠ s.points i)
    (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r := by
  rcases hp with ⟨w, hw, hw01, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra! hij
    simp_all
  obtain ⟨j, hij, hj⟩ : ∃ j, i ≠ j ∧ w j ≠ 0 := by
    by_contra! hij
    apply hp' i
    rw [← Finset.univ.affineCombination_affineCombinationSingleWeights ℝ s.points
      (Finset.mem_univ i)]
    congr 1
    ext j
    by_cases hj : j = i
    · simp only [hj, affineCombinationSingleWeights_apply_self]
      rw [← hw, eq_comm]
      exact sum_eq_single i (fun k _ hk ↦ hij k hk.symm) (by simp)
    · rw [affineCombinationSingleWeights_apply_of_ne _ hj]
      exact hij j (Ne.symm hj)
  exact dist_affineCombination_lt_of_strictConvexSpace (fun k _ ↦ (hw01 k).1) hw
    (Finset.mem_univ i) (Finset.mem_univ j) (s.independent.injective.ne hij) hi hj (fun k _ ↦ hr k)

lemma dist_lt_of_mem_interior_of_strictConvexSpace {n : ℕ} (s : Simplex ℝ P n) {r : ℝ}
    {p₀ p : P} (hp : p ∈ s.interior) (hr : ∀ i, dist (s.points i) p₀ ≤ r) : dist p p₀ < r :=
  s.dist_lt_of_mem_closedInterior_of_strictConvexSpace
    (Set.mem_of_mem_of_subset hp s.interior_subset_closedInterior)
    (fun i h ↦ s.point_notMem_interior i (h ▸ hp)) hr

end Simplex

end Affine

end Space
