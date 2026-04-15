/-
Extracted from Geometry/Euclidean/Angle/Oriented/Rotation.lean
Genuine: 36 | Conflates: 0 | Dissolved: 11 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/

noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}

variable [NormedAddCommGroup V] [NormedAddCommGroup V']

variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']

variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "J" => o.rightAngleRotation

def rotationAux (θ : Real.Angle) : V →ₗᵢ[ℝ] V :=
  LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination inner (𝕜 := ℝ) x y * θ.cos_sq_add_sin_sq)

@[simp]
theorem rotationAux_apply (θ : Real.Angle) (x : V) :
    o.rotationAux θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_smul, map_sub, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)
    (by
      ext x
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_add, map_smul, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)

theorem rotation_apply (θ : Real.Angle) (x : V) :
    o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

theorem rotation_symm_apply (θ : Real.Angle) (x : V) :
    (o.rotation θ).symm x = Real.Angle.cos θ • x - Real.Angle.sin θ • J x :=
  rfl

-- DISSOLVED: rotation_eq_matrix_toLin

@[simp]
theorem det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap = 1 := by
  haveI : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

@[simp]
theorem linearEquiv_det_rotation (θ : Real.Angle) :
    LinearEquiv.det (o.rotation θ).toLinearEquiv = 1 :=
  Units.ext <| by
    -- Porting note: Lean can't see through `LinearEquiv.coe_det` and needed the rewrite
    -- in mathlib3 this was just `units.ext <| o.det_rotation θ`
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

@[simp]
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) := by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

@[simp]
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl ℝ V := by ext; simp [rotation]

@[simp]
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  simp [rotation]

theorem rotation_pi_apply (x : V) : o.rotation π x = -x := by simp

theorem rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J := by
  ext x
  simp [rotation]

@[simp]
theorem rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) :
    o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x := by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, LinearIsometryEquiv.map_add,
    LinearIsometryEquiv.trans_apply, map_smul, rightAngleRotation_rightAngleRotation]
  module

@[simp]
theorem rotation_trans (θ₁ θ₂ : Real.Angle) :
    (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

@[simp]
theorem kahler_rotation_left (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = conj (θ.toCircle : ℂ) * o.kahler x y := by
  -- Porting note: this needed the `Complex.conj_ofReal` instead of `RCLike.conj_ofReal`;
  -- I believe this is because the respective coercions are no longer defeq, and
  -- `Real.Angle.coe_toCircle` uses the `Complex` version.
  simp only [o.rotation_apply, map_add, map_mul, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

theorem neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x := by
  rw [← o.rotation_pi_apply, rotation_rotation]

@[simp]
theorem neg_rotation_neg_pi_div_two (x : V) :
    -o.rotation (-π / 2 : ℝ) x = o.rotation (π / 2 : ℝ) x := by
  rw [neg_rotation, ← Real.Angle.coe_add, neg_div, ← sub_eq_add_neg, sub_half]

theorem neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : ℝ) x = o.rotation (-π / 2 : ℝ) x :=
  (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

theorem kahler_rotation_left' (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = (-θ).toCircle * o.kahler x y := by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

@[simp]
theorem kahler_rotation_right (x y : V) (θ : Real.Angle) :
    o.kahler x (o.rotation θ y) = θ.toCircle * o.kahler x y := by
  simp only [o.rotation_apply, map_add, LinearMap.map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

-- DISSOLVED: oangle_rotation_left

-- DISSOLVED: oangle_rotation_right

-- DISSOLVED: oangle_rotation_self_left

-- DISSOLVED: oangle_rotation_self_right

@[simp]
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]

@[simp]
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 := by
  rw [oangle_rev]
  simp

@[simp]
theorem oangle_rotation (x y : V) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

-- DISSOLVED: rotation_eq_self_iff_angle_eq_zero

-- DISSOLVED: eq_rotation_self_iff_angle_eq_zero

theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases h : x = 0 <;> simp [h]

theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff, eq_comm]

@[simp]
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ := by
  constructor
  · intro h
    rw [← h, LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

-- DISSOLVED: oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero

-- DISSOLVED: oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero

-- DISSOLVED: oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero

-- DISSOLVED: oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero

theorem exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < LinearMap.det (f.toLinearEquiv : V →ₗ[ℝ] V)) :
    ∃ θ : Real.Angle, f = o.rotation θ := by
  haveI : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  symm
  fin_cases i
  · simp
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x) := by
    simp only [oangle, o.linearIsometryEquiv_comp_rightAngleRotation f hd,
      o.kahler_comp_rightAngleRotation]
  simp [← this]

theorem rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x)) := by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]
protected theorem _root_.Complex.rotation (θ : Real.Angle) (z : ℂ) :
    Complex.orientation.rotation θ z = θ.toCircle * z := by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring

theorem rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (o.rotation θ x) = θ.toCircle * f x := by
  rw [← Complex.rotation, ← hf, o.rotation_map, LinearIsometryEquiv.symm_apply_apply]

theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) :=
  LinearIsometryEquiv.ext <| by simp [rotation_apply]

@[simp]
theorem inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [rotation_pi_div_two, inner_rightAngleRotation_self]

@[simp]
theorem inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left]

@[simp]
theorem inner_smul_rotation_pi_div_two_left (x : V) (r : ℝ) :
    ⟪r • o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [inner_smul_left, inner_rotation_pi_div_two_left, mul_zero]

@[simp]
theorem inner_smul_rotation_pi_div_two_right (x : V) (r : ℝ) :
    ⟪x, r • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_left]

@[simp]
theorem inner_rotation_pi_div_two_left_smul (x : V) (r : ℝ) :
    ⟪o.rotation (π / 2 : ℝ) x, r • x⟫ = 0 := by
  rw [inner_smul_right, inner_rotation_pi_div_two_left, mul_zero]

@[simp]
theorem inner_rotation_pi_div_two_right_smul (x : V) (r : ℝ) :
    ⟪r • x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left_smul]

@[simp]
theorem inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : ℝ) :
    ⟪r₁ • o.rotation (π / 2 : ℝ) x, r₂ • x⟫ = 0 := by
  rw [inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero]

@[simp]
theorem inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : ℝ) :
    ⟪r₂ • x, r₁ • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_smul_left]

theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
    ⟪x, y⟫ = 0 ↔ x = 0 ∨ ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) x = y := by
  rw [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (rfl | rfl | h | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, zero_smul _ _⟩
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero (o.left_ne_zero_of_oangle_eq_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_pi_div_two h) _).1 h
      exact Or.inr ⟨r, rfl⟩
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
          (o.left_ne_zero_of_oangle_eq_neg_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_neg_pi_div_two h) _).1 h
      refine Or.inr ⟨-r, ?_⟩
      rw [neg_smul, ← smul_neg, o.neg_rotation_pi_div_two]
  · rcases h with (rfl | ⟨r, rfl⟩)
    · exact Or.inl rfl
    · by_cases hx : x = 0; · exact Or.inl hx
      rcases lt_trichotomy r 0 with (hr | rfl | hr)
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [o.oangle_smul_right_of_neg _ _ hr, o.neg_rotation_pi_div_two,
          o.oangle_rotation_self_right hx]
      · exact Or.inr (Or.inl (zero_smul _ _))
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]

end Orientation
