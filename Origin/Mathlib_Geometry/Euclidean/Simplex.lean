/-
Extracted from Geometry/Euclidean/Simplex.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Simplices in Euclidean spaces.

This file defines properties of simplices in a Euclidean space.

## Main definitions

* `Affine.Simplex.AcuteAngled`

-/

namespace Affine

open EuclideanGeometry

open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : ℕ}

lemma Equilateral.angle_eq_pi_div_three {s : Simplex ℝ P n} (he : s.Equilateral)
    {i₁ i₂ i₃ : Fin (n + 1)} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) = π / 3 := by
  rcases he with ⟨r, hr⟩
  rw [angle, InnerProductGeometry.angle,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  refine Real.arccos_eq_of_eq_cos (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg]) ?_
  simp only [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, hr _ _ h₁₂, hr _ _ h₁₃,
    hr _ _ h₂₃.symm, Real.cos_pi_div_three]
  have hr0 : r ≠ 0 := by
    rintro rfl
    replace hr := hr _ _ h₁₂
    rw [dist_eq_zero] at hr
    exact h₁₂ (s.independent.injective hr)
  field

def AcuteAngled (s : Simplex ℝ P n) : Prop :=
  ∀ i₁ i₂ i₃ : Fin (n + 1), i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) < π / 2
