/-
Extracted from Analysis/Normed/Module/RCLike/Real.lean
Genuine: 4 of 11 | Dissolved: 6 | Infrastructure: 1
-/
import Origin.Core

/-!
# Basic facts about real (semi)normed spaces

In this file we prove some theorems about (semi)normed spaces over real numbers.

## Main results

- `closure_ball`, `frontier_ball`, `interior_closedBall`, `frontier_closedBall`, `interior_sphere`,
  `frontier_sphere`: formulas for the closure/interior/frontier
  of nontrivial balls and spheres in a real seminormed space;

- `interior_closedBall'`, `frontier_closedBall'`, `interior_sphere'`, `frontier_sphere'`:
  similar lemmas assuming that the ambient space is separated and nontrivial instead of `r ≠ 0`.
-/

open Metric Set Function Filter

open scoped NNReal Topology

-- INSTANCE (free from Core): Real.punctured_nhds_module_neBot

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_norm_smul_mem_unitClosedBall (x : E) :
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

variable [NontrivialTopology E]

section Surj

variable (E)

theorem exists_norm_eq {c : ℝ} (hc : 0 ≤ c) : ∃ x : E, ‖x‖ = c := by
  rcases exists_norm_ne_zero E with ⟨x, hx⟩
  use c • ‖x‖⁻¹ • x
  simp [norm_smul, Real.norm_of_nonneg hc, inv_mul_cancel₀ hx]
