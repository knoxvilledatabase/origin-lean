/-
Extracted from Analysis/NormedSpace/Real.lean
Genuine: 11 of 18 | Dissolved: 6 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Basic facts about real (semi)normed spaces

In this file we prove some theorems about (semi)normed spaces over real numberes.

## Main results

- `closure_ball`, `frontier_ball`, `interior_closedBall`, `frontier_closedBall`, `interior_sphere`,
  `frontier_sphere`: formulas for the closure/interior/frontier
  of nontrivial balls and spheres in a real seminormed space;

- `interior_closedBall'`, `frontier_closedBall'`, `interior_sphere'`, `frontier_sphere'`:
  similar lemmas assuming that the ambient space is separated and nontrivial instead of `r ≠ 0`.
-/

open Metric Set Function Filter

open scoped NNReal Topology

instance Real.punctured_nhds_module_neBot {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [ContinuousAdd E] [Nontrivial E] [Module ℝ E] [ContinuousSMul ℝ E] (x : E) : NeBot (𝓝[≠] x) :=
  Module.punctured_nhds_neBot ℝ E x

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_norm_smul_mem_closed_unit_ball (x : E) :
    ‖x‖⁻¹ • x ∈ closedBall (0 : E) 1 := by
  simp only [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, ← div_eq_inv_mul,
    div_self_le_one]

theorem norm_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : E) : ‖t • x‖ = t * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

theorem dist_smul_add_one_sub_smul_le {r : ℝ} {x y : E} (h : r ∈ Icc 0 1) :
    dist (r • x + (1 - r) • y) x ≤ dist y x :=
  calc
    dist (r • x + (1 - r) • y) x = ‖1 - r‖ * ‖x - y‖ := by
      simp_rw [dist_eq_norm', ← norm_smul, sub_smul, one_smul, smul_sub, ← sub_sub, ← sub_add,
        sub_right_comm]
    _ = (1 - r) * dist y x := by
      rw [Real.norm_eq_abs, abs_eq_self.mpr (sub_nonneg.mpr h.2), dist_eq_norm']
    _ ≤ (1 - 0) * dist y x := by gcongr; exact h.1
    _ = dist y x := by rw [sub_zero, one_mul]

-- DISSOLVED: closure_ball

-- DISSOLVED: frontier_ball

-- DISSOLVED: interior_closedBall

-- DISSOLVED: frontier_closedBall

-- DISSOLVED: interior_sphere

-- DISSOLVED: frontier_sphere

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

section Surj

variable (E)

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rw [← norm_ne_zero_iff] at hx
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, abs_of_nonneg hc, inv_mul_cancel₀ hx]

@[simp]
theorem range_norm : range (norm : E → ℝ) = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 norm_nonneg) fun _ => exists_norm_eq E

theorem nnnorm_surjective : Surjective (nnnorm : E → ℝ≥0) := fun c =>
  (exists_norm_eq E c.coe_nonneg).imp fun _ h => NNReal.eq h

@[simp]
theorem range_nnnorm : range (nnnorm : E → ℝ≥0) = univ :=
  (nnnorm_surjective E).range_eq

end Surj

theorem interior_closedBall' (x : E) (r : ℝ) : interior (closedBall x r) = ball x r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero, ball_zero, interior_singleton]
  · exact interior_closedBall x hr

theorem frontier_closedBall' (x : E) (r : ℝ) : frontier (closedBall x r) = sphere x r := by
  rw [frontier, closure_closedBall, interior_closedBall' x r, closedBall_diff_ball]

@[simp]
theorem interior_sphere' (x : E) (r : ℝ) : interior (sphere x r) = ∅ := by
  rw [← frontier_closedBall' x, interior_frontier isClosed_ball]

@[simp]
theorem frontier_sphere' (x : E) (r : ℝ) : frontier (sphere x r) = sphere x r := by
  rw [isClosed_sphere.frontier_eq, interior_sphere' x, diff_empty]

end Normed
