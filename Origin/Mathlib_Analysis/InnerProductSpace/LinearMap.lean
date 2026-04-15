/-
Extracted from Analysis/InnerProductSpace/LinearMap.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear maps on inner product spaces

This file studies linear maps on inner product spaces.

## Main results

- We define `innerSL` as the inner product bundled as a continuous sesquilinear map
- We prove a general polarization identity for linear maps (`inner_map_polarization`)
- We show that a linear map preserving the inner product is an isometry
  (`LinearMap.isometryOfInner`) and conversely an isometry preserves the inner product
  (`LinearIsometry.inner_map_map`).

## Tags

inner product space, Hilbert space, norm

-/

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section Complex_Seminormed

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring

end Complex_Seminormed

section Complex

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    rw [LinearMap.zero_apply, ← @inner_self_eq_zero ℂ V, inner_map_polarization]
    simp only [hT]
    simp
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]

theorem ext_inner_map (S T : V →ₗ[ℂ] V) : (∀ x : V, ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) ↔ S = T := by
  rw [← sub_eq_zero, ← inner_map_self_eq_zero]
  refine forall_congr' fun x => ?_
  rw [LinearMap.sub_apply, inner_sub_left, sub_eq_zero]

end Complex

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}

variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']
