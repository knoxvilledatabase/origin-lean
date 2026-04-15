/-
Extracted from Analysis/Convex/Uniform.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Uniformly convex spaces

This file defines uniformly convex spaces, which are real normed vector spaces in which for all
strictly positive `ε`, there exists some strictly positive `δ` such that `ε ≤ ‖x - y‖` implies
`‖x + y‖ ≤ 2 - δ` for all `x` and `y` of norm at most than `1`. This means that the triangle
inequality is strict with a uniform bound, as opposed to strictly convex spaces where the triangle
inequality is strict but not necessarily uniformly (`‖x + y‖ < ‖x‖ + ‖y‖` for all `x` and `y` not in
the same ray).

## Main declarations

`UniformConvexSpace E` means that `E` is a uniformly convex space.

## TODO

* Milman-Pettis
* Hanner's inequalities

## Tags

convex, uniformly convex
-/

open Set Metric

open Convex Pointwise

class UniformConvexSpace (E : Type*) [SeminormedAddCommGroup E] : Prop where
  uniform_convex : ∀ ⦃ε : ℝ⦄,
    0 < ε → ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ

variable {E : Type*}

section SeminormedAddCommGroup

variable (E) [SeminormedAddCommGroup E] [UniformConvexSpace E] {ε : ℝ}

theorem exists_forall_sphere_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ = 1 → ∀ ⦃y⦄, ‖y‖ = 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ :=
  UniformConvexSpace.uniform_convex hε

variable [NormedSpace ℝ E]

theorem exists_forall_closed_ball_dist_add_le_two_sub (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ ≤ 1 → ∀ ⦃y⦄, ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ → ‖x + y‖ ≤ 2 - δ := by
  have hε' : 0 < ε / 3 := div_pos hε zero_lt_three
  obtain ⟨δ, hδ, h⟩ := exists_forall_sphere_dist_add_le_two_sub E hε'
  set δ' := min (1 / 2) (min (ε / 3) <| δ / 3)
  refine ⟨δ', lt_min one_half_pos <| lt_min hε' (div_pos hδ zero_lt_three), fun x hx y hy hxy => ?_⟩
  obtain hx' | hx' := le_or_gt ‖x‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx' hy).trans (sub_add_eq_add_sub _ _ _).le
  obtain hy' | hy' := le_or_gt ‖y‖ (1 - δ')
  · rw [← one_add_one_eq_two]
    exact (norm_add_le_of_le hx hy').trans (add_sub_assoc _ _ _).ge
  have hδ' : 0 < 1 - δ' := sub_pos_of_lt (min_lt_of_left_lt one_half_lt_one)
  have h₁ : ∀ z : E, 1 - δ' < ‖z‖ → ‖‖z‖⁻¹ • z‖ = 1 := by
    rintro z hz
    rw [norm_smul_of_nonneg (inv_nonneg.2 <| norm_nonneg _), inv_mul_cancel₀ (hδ'.trans hz).ne']
  have h₂ : ∀ z : E, ‖z‖ ≤ 1 → 1 - δ' ≤ ‖z‖ → ‖‖z‖⁻¹ • z - z‖ ≤ δ' := by
    rintro z hz hδz
    nth_rw 3 [← one_smul ℝ z]
    rwa [← sub_smul,
      norm_smul_of_nonneg (sub_nonneg_of_le <| (one_le_inv₀ (hδ'.trans_le hδz)).2 hz),
      sub_mul, inv_mul_cancel₀ (hδ'.trans_le hδz).ne', one_mul, sub_le_comm]
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hxy' : ε / 3 ≤ ‖x' - y'‖ :=
    calc
      ε / 3 = ε - (ε / 3 + ε / 3) := by ring
      _ ≤ ‖x - y‖ - (‖x' - x‖ + ‖y' - y‖) := by
        gcongr
        · exact (h₂ _ hx hx'.le).trans <| min_le_of_right_le <| min_le_left _ _
        · exact (h₂ _ hy hy'.le).trans <| min_le_of_right_le <| min_le_left _ _
      _ ≤ _ := by
        have : ∀ x' y', x - y = x' - y' + (x - x') + (y' - y) := fun _ _ => by abel
        rw [sub_le_iff_le_add, norm_sub_rev _ x, ← add_assoc, this]
        exact norm_add₃_le
  calc
    ‖x + y‖ ≤ ‖x' + y'‖ + ‖x' - x‖ + ‖y' - y‖ := by
      have : ∀ x' y', x + y = x' + y' + (x - x') + (y - y') := fun _ _ => by abel
      rw [norm_sub_rev, norm_sub_rev y', this]
      exact norm_add₃_le
    _ ≤ 2 - δ + δ' + δ' := by
      gcongr
      exacts [h (h₁ _ hx') (h₁ _ hy') hxy', h₂ _ hx hx'.le, h₂ _ hy hy'.le]
    _ ≤ 2 - δ' := by
      suffices δ' ≤ δ / 3 by linarith
      exact min_le_of_right_le <| min_le_right _ _

end SeminormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

-- INSTANCE (free from Core): (priority
