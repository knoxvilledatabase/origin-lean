/-
Extracted from Geometry/Euclidean/Angle/Unoriented/TriangleInequality.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The Triangle Inequality for Angles

This file contains the proof that angles obey the triangle inequality.
-/

open InnerProductGeometry

open NormedSpace

open scoped Real NNReal RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

section UnitVectorAngles

noncomputable def ortho (x y : V) : V := y - (ℝ ∙ x).starProjection y

lemma ortho_eq_sub_inner (x : V) {y : V} (hy : ‖y‖ = 1) : ortho y x = x - inner ℝ y x • y := by
  rw [ortho, Submodule.starProjection_unit_singleton _ hy]

lemma inner_ortho_nonneg {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 0 ≤ ⟪x, ortho y x⟫ := by
  rw [ortho_eq_sub_inner x hy, inner_sub_right,
    inner_self_eq_one_of_norm_eq_one hx, real_inner_smul_right, real_inner_comm, sub_nonneg]
  grw [← sq, sq_le_one_iff_abs_le_one, abs_real_inner_le_norm, hx, hy, one_mul]
